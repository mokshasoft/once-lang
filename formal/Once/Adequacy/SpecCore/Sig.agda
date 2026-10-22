{-# OPTIONS --guardedness #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.SpecCore.Sig — a Spec Interpretation, read as the compiler's,
-- agrees with itself (plan 0.121 §3.5).
--
-- `SpecInterp` reads a Spec Interpretation `J` of Σ as the compiler's: an
-- implementation of `toISig Σ` (`toImpl`) and so an interpretation
-- (`toInterp`). Against it, the compiler's reference to a declaration means
-- the Spec's (`sig-G`, the hypothesis of `Program.teleR`), and its calls are
-- answered and observed as the Spec's (`agree`, the hypothesis of
-- `Observe.observe-R`).
--
-- The compiler finds a declaration by its RENDERED name (`showCanonical`); the
-- reading is the declaration's when no two of Σ's declarations render alike
-- (`uniq`). Each reading of `toImpl` is first described by the declaration it
-- comes from (`PureG`, `AnsG`), then pinned to it by that uniqueness.
------------------------------------------------------------------------

open import Data.List using (List; map)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
open import Once.Internal.Name using (showCanonical; WordName)
open import Once.Spec.Numerics using (TargetNum)
open import Once.Spec.Signature using (Signature; WellFormed; Decl)
import Once.Spec.Observation as Obs

module Once.Adequacy.SpecCore.Sig
  (Σ : Signature) (wf : WellFormed Σ) (J : Obs.Interp Σ)
  (uniq : Unique (map (λ d → showCanonical (Decl.name d)) Σ)) (fmt : TargetNum) where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([]; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁺)
open import Data.List.Relation.Unary.Any using (here; there)
import Data.List.Relation.Unary.All as All
open import Data.List.Relation.Unary.AllPairs using (_∷_)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.String using (String)
open import Data.Unit using (⊤; tt)
open import Data.Maybe using (just)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Nullary using (Dec; yes; no; ¬_)

open import Once.Spec.Word using (Carrier)
import Once.Internal.Value Carrier Carrier as M
import Once.Internal.Type as T
import Once.Spec.Type as T
import Once.Spec.Grade as G
import Once.Internal.Type.WellFormed as LW
import Once.Internal.Type.Honest as LH
import Once.Internal.GradedOps as LOps
import Once.Internal.Trace as LTr
open import Once.Internal.Event using (SigOpEvent; toEvent; baseOf; valOf)
open import Once.Internal.Contract using (Key; key; kname; kdom; kcod; valueKeys; answerKeys; value-step; answer-step; valueOf; valueOf-at; _∈K?_; Impl)
open import Once.Internal.ContractLaws using (value-∈; base-contract)
import Once.Spec.Grade as SG
import Once.Spec.Type as ST
import Once.Spec.Signature as S
open S using (DeclType; constant; value; operation; _∶_; argAt; NotEmpty; notEmpty?; op; Op; ⌜_⌝ᵈ)
import Once.Spec.Domain Σ as SD
import Once.Spec.Effect Σ as SE
import Once.Spec.Core.Syntax as SC
import Once.Spec.Core.Meaning as SM
open Obs Σ using (Model; World; module Model; module World)
import Once.Adequacy.SpecInterp as SI
open SI using (toISig; declTy; ⌞_⌟; qL; toImpl; toInterp)
open import Once.Adequacy.SpecCore.Poly using (declS)
open import Once.Adequacy.SpecCore.DeclType using (toB-⌞⌟; declS-declTy)
open import Once.Adequacy.SpecCore.Index
open import Once.Adequacy.SpecCore.Value Σ
open import Once.Adequacy.SpecCore.Observe Σ using (Agree)
import Once.Adequacy.SpecCore.Program as PG

private
  sname : Decl → String
  sname d = showCanonical (Decl.name d)

  I : Impl (toISig Σ)
  I = toImpl Σ J wf

  mo : Model
  mo = Obs.Interp.model J

  w : World
  w = Obs.Interp.world J

------------------------------------------------------------------------
-- Σ's declarations, by rendered name
------------------------------------------------------------------------

-- Two declarations of a list with distinct rendered names, rendered alike,
-- are one.
one-decl : ∀ {Σ′ : Signature} → Unique (map sname Σ′) → ∀ {d₁ d₂} (m₁ : d₁ ∈ Σ′) (m₂ : d₂ ∈ Σ′)
         → sname d₁ ≡ sname d₂ → _≡_ {A = Σ[ d ∈ Decl ] d ∈ Σ′} (d₁ , m₁) (d₂ , m₂)
one-decl (h ∷ u) (here refl) (here refl) e = refl
one-decl (h ∷ u) (here refl) (there m₂)  e = ⊥-elim (All.lookup h (∈-map⁺ sname m₂) e)
one-decl (h ∷ u) (there m₁)  (here refl) e = ⊥-elim (All.lookup h (∈-map⁺ sname m₁) (sym e))
one-decl (h ∷ u) (there m₁)  (there m₂)  e = cong (λ { (d , m) → d , there m }) (one-decl u m₁ m₂ e)

-- A compiler declaration is a Spec one, at its type read as the compiler's.
mem-view : ∀ {Σ′ : Signature} {s A} → (s , A) ∈ toISig Σ′
         → Σ[ d ∈ Decl ] (d ∈ Σ′) × (sname d ≡ s) × (declTy (Decl.type d) ≡ A)
mem-view {(c ∶ t) ∷ Σ′} (here refl) = (c ∶ t) , here refl , refl , refl
mem-view {_ ∷ Σ′} (there m) with mem-view {Σ′} m
... | d , md , es , eA = d , there md , es , eA

wf-at : ∀ {Σ′ : Signature} → WellFormed Σ′ → ∀ {d} → d ∈ Σ′ → S.WellFormedDecl (Decl.type d)
wf-at (x S.∷ _)  (here refl) = x
wf-at (_ S.∷ ws) (there m)   = wf-at ws m

------------------------------------------------------------------------
-- Base types and values
------------------------------------------------------------------------

base-of : ∀ b .(ib : LW.IsBaseType ⌞ b ⌟) → baseOf ⌞ b ⌟ ib ≡ b
base-of S.unit    _ = refl
base-of S.void    _ = refl
base-of S.int     _ = refl
base-of S.float   _ = refl
base-of (a S.* b) _ = cong₂ S._*_ (base-of a _) (base-of b _)
base-of (a S.+ b) _ = cong₂ S._+_ (base-of a _) (base-of b _)

-- A base type read as the compiler's is `Void`, or `Unit`, only as itself.
⌞⌟-void : ∀ b → ⌞ b ⌟ ≡ T.Void → b ≡ S.void
⌞⌟-void S.void refl = refl
⌞⌟-void S.unit  ()
⌞⌟-void S.int   ()
⌞⌟-void S.float ()
⌞⌟-void (a S.* b) ()
⌞⌟-void (a S.+ b) ()

⌞⌟-unit : ∀ b → ⌞ b ⌟ ≡ T.Unit → b ≡ S.unit
⌞⌟-unit S.unit refl = refl
⌞⌟-unit S.void  ()
⌞⌟-unit S.int   ()
⌞⌟-unit S.float ()
⌞⌟-unit (a S.* b) ()
⌞⌟-unit (a S.+ b) ()

-- A base value, read into the compiler's graded domain and into the Spec's.
module _ {m} (σ′ : ST.TySub m 0) where

  base-R : ∀ b (ib : LW.IsBaseType ⌞ b ⌟) (g : GR ⌞ b ⌟ (S.⌜ b ⌝ ST.⟨ σ′ ⟩)) (v : S.⟦ b ⟧ᵇ)
         → ValR g (LOps.injB ib (SI.fromB b v)) (SD.fromB σ′ b v)
  base-R S.unit  LW.base-Unit  g-unit  v = tt
  base-R S.void  LW.base-Void  g-void  v = tt
  base-R S.int   LW.base-Int   g-int   v = refl
  base-R S.float LW.base-Float g-float v = refl
  base-R (a S.* b) (LW.base-Prod ia ib) (g-* ga gb) (x , y) = base-R a ia ga x , base-R b ib gb y
  base-R (a S.+ b) (LW.base-Sum ia ib) (g-+ ga gb) (inj₁ x) = base-R a ia ga x
  base-R (a S.+ b) (LW.base-Sum ia ib) (g-+ ga gb) (inj₂ y) = base-R b ib gb y

  toB-R : ∀ b (ib : LW.IsBaseType ⌞ b ⌟) (g : GR ⌞ b ⌟ (S.⌜ b ⌝ ST.⟨ σ′ ⟩)) {x y}
        → ValR g x y → SI.toB b (LOps.prjB ib x) ≡ SD.toB σ′ b y
  toB-R S.unit  LW.base-Unit  g-unit  r = refl
  toB-R S.void  LW.base-Void  g-void  {()} r
  toB-R S.int   LW.base-Int   g-int   r = r
  toB-R S.float LW.base-Float g-float r = r
  toB-R (a S.* b) (LW.base-Prod ia ib) (g-* ga gb) {_ , _} {_ , _} (r , r′) =
    cong₂ _,_ (toB-R a ia ga r) (toB-R b ib gb r′)
  toB-R (a S.+ b) (LW.base-Sum ia ib) (g-+ ga gb) {inj₁ _} {inj₁ _} r = cong inj₁ (toB-R a ia ga r)
  toB-R (a S.+ b) (LW.base-Sum ia ib) (g-+ ga gb) {inj₂ _} {inj₂ _} r = cong inj₂ (toB-R b ib gb r)
  toB-R (a S.+ b) (LW.base-Sum ia ib) (g-+ ga gb) {inj₁ _} {inj₂ _} ()
  toB-R (a S.+ b) (LW.base-Sum ia ib) (g-+ ga gb) {inj₂ _} {inj₁ _} ()

-- An event, read as the Spec's, at a declaration's argument type.
private
  BV′ : Set
  BV′ = Σ[ b ∈ S.BTy ] S.⟦ b ⟧ᵇ

  ev-p : ∀ {p q : BV′} {a′ b′ x′ y′} → p ≡ (a′ , x′) → q ≡ (b′ , y′)
       → _≡_ {A = BV′} (proj₁ p S.* proj₁ q , (proj₂ p , proj₂ q)) (a′ S.* b′ , (x′ , y′))
  ev-p refl refl = refl

  ev-l : ∀ {p : BV′} {a′ x′} {b″ b′ : S.BTy} → p ≡ (a′ , x′) → b″ ≡ b′
       → _≡_ {A = BV′} (proj₁ p S.+ b″ , inj₁ (proj₂ p)) (a′ S.+ b′ , inj₁ x′)
  ev-l refl refl = refl

  ev-r : ∀ {q : BV′} {b′ y′} {a″ a′ : S.BTy} → q ≡ (b′ , y′) → a″ ≡ a′
        → _≡_ {A = BV′} (a″ S.+ proj₁ q , inj₂ (proj₂ q)) (a′ S.+ b′ , inj₂ y′)
  ev-r refl refl = refl

ev-val : ∀ a .(ib : LW.IsBaseType ⌞ a ⌟) (x : M.⟦ ⌞ a ⌟ ⟧)
       → _≡_ {A = BV′} (baseOf ⌞ a ⌟ ib , valOf ⌞ a ⌟ ib x) (a , SI.toB a x)
ev-val S.unit  _ x = refl
ev-val S.void  _ x = refl
ev-val S.int   _ x = refl
ev-val S.float _ x = refl
ev-val (a S.* b) _ (x , y)  = ev-p (ev-val a _ x) (ev-val b _ y)
ev-val (a S.+ b) _ (inj₁ x) = ev-l (ev-val a _ x) (base-of b _)
ev-val (a S.+ b) _ (inj₂ y) = ev-r (ev-val b _ y) (base-of a _)

------------------------------------------------------------------------
-- What `toImpl` reads, by the declaration it reads
------------------------------------------------------------------------

Fn : Key → Set
Fn k = M.⟦ kdom k ⟧ → M.⟦ kcod k ⟧

-- A value key reads the model at a constant or a pure function of Σ.
data PureG : (k : Key) → Fn k → Set where
  pg-const : ∀ {c b} (m : (c ∶ constant b) ∈ Σ)
           → PureG (key (showCanonical c) T.Unit ⌞ b ⌟) (λ _ → SI.fromB b (Model.constantᵐ mo m))
  pg-value : ∀ {c a q b} (m : (c ∶ value a q b) ∈ Σ)
           → PureG (key (showCanonical c) ⌞ argAt q a ⌟ ⌞ b ⌟) (λ x → SI.fromB b (Model.valueᵐ mo m (SI.toB (argAt q a) x)))

pure-G : ∀ (Σ′ : Signature) (inj : ∀ {d} → d ∈ Σ′ → d ∈ Σ) k (p : k ∈ valueKeys (toISig Σ′)) → PureG k (SI.pureAt Σ J Σ′ inj k p)
pure-step : ∀ {c t ct} (Σ′ : Signature) (inj : ∀ {d} → d ∈ ((c ∶ t) ∷ Σ′) → d ∈ Σ) (dc : SI.DeclContract (showCanonical c) t ct)
            k (p : k ∈ value-step ct (valueKeys (toISig Σ′))) → PureG k (SI.pureStep Σ J Σ′ inj dc k p)
pure-G []              inj k ()
pure-G ((c ∶ t) ∷ Σ′) inj k p = pure-step Σ′ inj (SI.declContract (showCanonical c) t) k p
pure-step {t = constant b}  Σ′ inj SI.dc-const k (here refl) = pg-const (inj (here refl))
pure-step {t = value a q b} Σ′ inj SI.dc-value k (here refl) = pg-value (inj (here refl))
pure-step Σ′ inj SI.dc-const           k (there p) = pure-G Σ′ (λ m → inj (there m)) k p
pure-step Σ′ inj SI.dc-value           k (there p) = pure-G Σ′ (λ m → inj (there m)) k p
pure-step Σ′ inj (SI.dc-op-answer _ _) k p         = pure-G Σ′ (λ m → inj (there m)) k p
pure-step Σ′ inj SI.dc-op-effect       k p         = pure-G Σ′ (λ m → inj (there m)) k p

-- …so a value key of a declaration reads that declaration.
pure-const : ∀ {k f} → PureG k f → ∀ {c b} (m : (c ∶ constant b) ∈ Σ) (e : k ≡ key (showCanonical c) T.Unit ⌞ b ⌟)
           → subst Fn e f ≡ (λ _ → SI.fromB b (Model.constantᵐ mo m))
pure-const (pg-const m′) m e = pc (one-decl uniq m′ m (cong kname e)) e
  where
    pc : ∀ {c c′ b b′} {m : (c ∶ constant b) ∈ Σ} {m′ : (c′ ∶ constant b′) ∈ Σ}
       → _≡_ {A = Σ[ d ∈ Decl ] d ∈ Σ} ((c′ ∶ constant b′) , m′) ((c ∶ constant b) , m)
       → (e : key (showCanonical c′) T.Unit ⌞ b′ ⌟ ≡ key (showCanonical c) T.Unit ⌞ b ⌟)
       → subst Fn e (λ _ → SI.fromB b′ (Model.constantᵐ mo m′)) ≡ (λ _ → SI.fromB b (Model.constantᵐ mo m))
    pc refl refl = refl
pure-const (pg-value m′) m e = ⊥-elim (vc (one-decl uniq m′ m (cong kname e)))
  where
    vc : ∀ {c c′ a q b b′} {m : (c ∶ constant b) ∈ Σ} {m′ : (c′ ∶ value a q b′) ∈ Σ}
       → _≡_ {A = Σ[ d ∈ Decl ] d ∈ Σ} ((c′ ∶ value a q b′) , m′) ((c ∶ constant b) , m) → ⊥
    vc ()

pure-value : ∀ {k f} → PureG k f → ∀ {c a q b} (m : (c ∶ value a q b) ∈ Σ) (e : k ≡ key (showCanonical c) ⌞ argAt q a ⌟ ⌞ b ⌟)
           → subst Fn e f ≡ (λ x → SI.fromB b (Model.valueᵐ mo m (SI.toB (argAt q a) x)))
pure-value (pg-value m′) m e = pv (one-decl uniq m′ m (cong kname e)) e
  where
    pv : ∀ {c c′ a a′ q q′ b b′} {m : (c ∶ value a q b) ∈ Σ} {m′ : (c′ ∶ value a′ q′ b′) ∈ Σ}
       → _≡_ {A = Σ[ d ∈ Decl ] d ∈ Σ} ((c′ ∶ value a′ q′ b′) , m′) ((c ∶ value a q b) , m)
       → (e : key (showCanonical c′) ⌞ argAt q′ a′ ⌟ ⌞ b′ ⌟ ≡ key (showCanonical c) ⌞ argAt q a ⌟ ⌞ b ⌟)
       → subst Fn e (λ x → SI.fromB b′ (Model.valueᵐ mo m′ (SI.toB (argAt q′ a′) x)))
         ≡ (λ x → SI.fromB b (Model.valueᵐ mo m (SI.toB (argAt q a) x)))
    pv refl refl = refl
pure-value (pg-const m′) m e = ⊥-elim (cv (one-decl uniq m′ m (cong kname e)))
  where
    cv : ∀ {c c′ a q b b′} {m : (c ∶ value a q b) ∈ Σ} {m′ : (c′ ∶ constant b′) ∈ Σ}
       → _≡_ {A = Σ[ d ∈ Decl ] d ∈ Σ} ((c′ ∶ constant b′) , m′) ((c ∶ value a q b) , m) → ⊥
    cv ()

-- An answer key reads the world at an operation of Σ, after the calls `h`.
data AnsG (h : List SigOpEvent) : (k : Key) → Fn k → Set where
  ag : ∀ {c a q b} (m : (c ∶ operation a q b) ∈ Σ) (ne : NotEmpty b)
     → AnsG h (key (showCanonical c) ⌞ argAt q a ⌟ ⌞ b ⌟)
              (λ x → SI.fromB b (SI.answerAt-dec Σ J (op m) (map toEvent h) (SI.toB (argAt q a) x) (notEmpty? b) ne))

ans-G : ∀ (Σ′ : Signature) (inj : ∀ {d} → d ∈ Σ′ → d ∈ Σ) (wf′ : WellFormed Σ′) h k (p : k ∈ answerKeys (toISig Σ′))
      → AnsG h k (SI.answerAt Σ J Σ′ inj wf′ h k p)
ans-step : ∀ {c t ct} (Σ′ : Signature) (inj : ∀ {d} → d ∈ ((c ∶ t) ∷ Σ′) → d ∈ Σ) (w′ : S.WellFormedDecl t) (wf′ : WellFormed Σ′)
           (dc : SI.DeclContract (showCanonical c) t ct) h k (p : k ∈ answer-step ct (answerKeys (toISig Σ′)))
         → AnsG h k (SI.answerStep Σ J Σ′ inj w′ wf′ dc h k p)
ans-G []              inj wf′          h k ()
ans-G ((c ∶ t) ∷ Σ′) inj (w′ S.∷ wf′) h k p = ans-step Σ′ inj w′ wf′ (SI.declContract (showCanonical c) t) h k p
ans-step {t = operation a q b} Σ′ inj w′ wf′ (SI.dc-op-answer ¬v ¬u) h k (here refl) = ag (inj (here refl)) _
ans-step Σ′ inj w′ wf′ (SI.dc-op-answer _ _) h k (there p) = ans-G Σ′ (λ m → inj (there m)) wf′ h k p
ans-step Σ′ inj w′ wf′ SI.dc-const           h k p         = ans-G Σ′ (λ m → inj (there m)) wf′ h k p
ans-step Σ′ inj w′ wf′ SI.dc-value           h k p         = ans-G Σ′ (λ m → inj (there m)) wf′ h k p
ans-step Σ′ inj w′ wf′ SI.dc-op-effect       h k p         = ans-G Σ′ (λ m → inj (there m)) wf′ h k p

-- …so an operation's answer key reads that operation, at the decided inhabitant.
ans-op : ∀ {h k f} → AnsG h k f → ∀ {c a b} (m : (c ∶ operation a SG.Many b) ∈ Σ) (e : k ≡ key (showCanonical c) ⌞ a ⌟ ⌞ b ⌟)
       → ∀ p → notEmpty? b ≡ yes p → ∀ x
       → subst Fn e f x ≡ SI.fromB b (World.answer w (op m) (map toEvent h) (SI.toB a x) p)
ans-op {h} (ag m′ ne) m e p d x = ao (one-decl uniq m′ m (cong kname e)) e x p d
  where
    ao : ∀ {c c′ a a′ q′ b b′} {m : (c ∶ operation a SG.Many b) ∈ Σ} {m′ : (c′ ∶ operation a′ q′ b′) ∈ Σ} {ne : NotEmpty b′}
       → _≡_ {A = Σ[ d ∈ Decl ] d ∈ Σ} ((c′ ∶ operation a′ q′ b′) , m′) ((c ∶ operation a SG.Many b) , m)
       → (e : key (showCanonical c′) ⌞ argAt q′ a′ ⌟ ⌞ b′ ⌟ ≡ key (showCanonical c) ⌞ a ⌟ ⌞ b ⌟) → ∀ x p
       → notEmpty? b ≡ yes p
       → subst Fn e (λ x → SI.fromB b′ (SI.answerAt-dec Σ J (op m′) (map toEvent h) (SI.toB (argAt q′ a′) x) (notEmpty? b′) ne)) x
         ≡ SI.fromB b (World.answer w (op m) (map toEvent h) (SI.toB a x) p)
    ao {a = a} {b = b} {m = m} {ne = ne} refl refl x p d′ =
      cong (λ dd → SI.fromB b (SI.answerAt-dec Σ J (op m) (map toEvent h) (SI.toB a x) dd ne)) d′

------------------------------------------------------------------------
-- The declarations: the compiler's reference means the Spec's
------------------------------------------------------------------------

private
  -- a constant's type is a base type
  const-k : ∀ b (k : LW.IsConcrete ⌞ b ⌟) → Σ[ ib ∈ LW.IsBaseType ⌞ b ⌟ ] (k ≡ LW.con-base ib)
  const-k S.unit      (LW.con-base ib) = ib , refl
  const-k S.void      (LW.con-base ib) = ib , refl
  const-k S.int       (LW.con-base ib) = ib , refl
  const-k S.float     (LW.con-base ib) = ib , refl
  const-k (a S.* b)   (LW.con-base ib) = ib , refl
  const-k (a S.+ b)   (LW.con-base ib) = ib , refl

  -- what `valueOf` reads at a declaration's key, through its decision
  read-const : ∀ {c b} (M : (c ∶ constant b) ∈ Σ) {p} (dec : Dec (key (showCanonical c) T.Unit ⌞ b ⌟ ∈ valueKeys (toISig Σ)))
             → valueOf-at I (key (showCanonical c) T.Unit ⌞ b ⌟) p dec tt ≡ SI.fromB b (Model.constantᵐ mo M)
  read-const M (yes p₀)    = cong (λ f → f tt) (pure-const (pure-G Σ (λ m → m) _ p₀) M refl)
  read-const M {p} (no ¬p) = ⊥-elim (¬p p)

  read-value : ∀ {c a q b} (M : (c ∶ value a q b) ∈ Σ) {p} (dec : Dec (key (showCanonical c) ⌞ argAt q a ⌟ ⌞ b ⌟ ∈ valueKeys (toISig Σ))) x
             → valueOf-at I (key (showCanonical c) ⌞ argAt q a ⌟ ⌞ b ⌟) p dec x ≡ SI.fromB b (Model.valueᵐ mo M (SI.toB (argAt q a) x))
  read-value M (yes p₀)    x = cong (λ f → f x) (pure-value (pure-G Σ (λ m → m) _ p₀) M refl)
  read-value M {p} (no ¬p) x = ⊥-elim (¬p p)

  data-ne : ∀ b → S.EffCod b → ⌞ b ⌟ ≢ T.Void → ⌞ b ⌟ ≢ T.Unit → NotEmpty b
  data-ne b (inj₁ refl)            ¬v ¬u = ⊥-elim (¬u refl)
  data-ne b (inj₂ (inj₁ refl))     ¬v ¬u = ⊥-elim (¬v refl)
  data-ne b (inj₂ (inj₂ (ne , _))) _  _  = ne

  ne-void : ∀ {b} → NotEmpty b → b ≢ S.void
  ne-void ne refl = ne

module _ {s₀} (S₀ : SC.Defs s₀) {m} (σ′ : ST.TySub m 0) where

  private
    -- an operation's call, by the form its answer type decides
    sig-halt : ∀ {c a b} (M : (c ∶ operation a SG.Many b) ∈ Σ) (bDom : LW.IsBaseType ⌞ a ⌟) (bCod : LW.IsBaseType ⌞ b ⌟)
               (ga : GR ⌞ a ⌟ (S.⌜ a ⌝ ST.⟨ σ′ ⟩)) (gb : GR ⌞ b ⌟ (S.⌜ b ⌝ ST.⟨ σ′ ⟩)) {x y} → ValR ga x y
             → b ≡ S.void → (e : ⌞ b ⌟ ≡ T.Void) → ∀ du
             → TR (ValR gb) (LTr.fmapT (LOps.injB bCod) (LOps.opCallᵀ c bDom (yes e) du (LOps.prjB bDom x)))
                            (SE.performT (S.call (op M) (SD.toB σ′ a y) (SD.fromB σ′ b)))
    sig-halt {a = a} M bDom bCod ga gb r refl refl du = halt (hr M) (toB-R σ′ a bDom ga r)

    sig-unit : ∀ {c a b} (M : (c ∶ operation a SG.Many b) ∈ Σ) (bDom : LW.IsBaseType ⌞ a ⌟) (bCod : LW.IsBaseType ⌞ b ⌟)
               (ga : GR ⌞ a ⌟ (S.⌜ a ⌝ ST.⟨ σ′ ⟩)) (gb : GR ⌞ b ⌟ (S.⌜ b ⌝ ST.⟨ σ′ ⟩)) {x y} → ValR ga x y
             → (¬v : ¬ (⌞ b ⌟ ≡ T.Void)) → b ≡ S.unit → (e : ⌞ b ⌟ ≡ T.Unit)
             → TR (ValR gb) (LTr.fmapT (LOps.injB bCod) (LOps.opCallᵀ c bDom (no ¬v) (yes e) (LOps.prjB bDom x)))
                            (SE.performT (S.call (op M) (SD.toB σ′ a y) (SD.fromB σ′ b)))
    sig-unit {a = a} M bDom bCod ga gb r ¬v refl refl =
      call (cr M tt) (toB-R σ′ a bDom ga r) (λ {v} {v′} _ → ret (base-R σ′ S.unit bCod gb v′))

    sig-op : ∀ {c a b} (M : (c ∶ operation a SG.Many b) ∈ Σ) (bDom : LW.IsBaseType ⌞ a ⌟) (bCod : LW.IsBaseType ⌞ b ⌟)
             (ga : GR ⌞ a ⌟ (S.⌜ a ⌝ ST.⟨ σ′ ⟩)) (gb : GR ⌞ b ⌟ (S.⌜ b ⌝ ST.⟨ σ′ ⟩)) {x y} → ValR ga x y
           → ∀ dv du
           → TR (ValR gb) (LTr.fmapT (LOps.injB bCod) (LOps.opCallᵀ c bDom dv du (LOps.prjB bDom x)))
                          (SE.performT (S.call (op M) (SD.toB σ′ a y) (SD.fromB σ′ b)))
    sig-op {b = b} M bDom bCod ga gb r (yes e) du      = sig-halt M bDom bCod ga gb r (⌞⌟-void b e) e du
    sig-op {b = b} M bDom bCod ga gb r (no ¬v) (yes e) = sig-unit M bDom bCod ga gb r ¬v (⌞⌟-unit b e) e
    sig-op {a = a} {b} M bDom bCod ga gb r (no ¬v) (no ¬u) =
      call (cr M (data-ne b (wf-at wf M) ¬v ¬u)) (toB-R σ′ a bDom ga r)
           (λ {v} {v′} e → ret (subst (λ z → ValR gb (LOps.injB bCod z) (SD.fromB σ′ b v′)) (sym e) (base-R σ′ b bCod gb v′)))

  -- At each form of declaration.
  sig-t : ∀ {c} t (k : LW.IsConcrete (declTy t)) (h : LH.HonestFFI (declTy t)) (mem : (showCanonical c , declTy t) ∈ toISig Σ)
          (gs : GR (declTy t) (⌜ t ⌝ᵈ ST.⟨ σ′ ⟩)) (M : (c ∶ t) ∈ Σ)
        → ValR gs (LOps.sigOpRefᵛ fmt (toISig Σ) I c k mem) (SM.sigopᵛ Σ fmt S₀ σ′ c t M mo)
  sig-c : ∀ {c} b (k : LW.IsConcrete ⌞ b ⌟) → Σ[ ib ∈ LW.IsBaseType ⌞ b ⌟ ] (k ≡ LW.con-base ib)
        → (mem : (showCanonical c , ⌞ b ⌟) ∈ toISig Σ) (gs : GR ⌞ b ⌟ (S.⌜ b ⌝ ST.⟨ σ′ ⟩)) (M : (c ∶ constant b) ∈ Σ)
        → ValR gs (LOps.sigOpRefᵛ fmt (toISig Σ) I c k mem) (SM.sigopᵛ Σ fmt S₀ σ′ c (constant b) M mo)
  sig-c b .(LW.con-base ib) (ib , refl) mem gs M =
    subst (λ v → ValR gs (LOps.injB ib v) (SD.fromB σ′ b (Model.constantᵐ mo M))) (sym (read-const M (_ ∈K? valueKeys (toISig Σ)))) (base-R σ′ b ib gs _)

  sig-t (constant b) k h mem gs M = sig-c b k (const-k b k) mem gs M
  sig-t (value a SG.Zero b) (LW.con-fun bDom bCod) h mem (g-⇒ ga gb) M =
    subst (λ v → ValR gb (LOps.injB bCod v) (SD.fromB σ′ b (Model.valueᵐ mo M tt))) (sym (read-value M (_ ∈K? valueKeys (toISig Σ)) tt)) (base-R σ′ b bCod gb _)
  sig-t (value a SG.One b) (LW.con-fun bDom bCod) h mem (g-⇒ ga gb) M {x} {y} r =
    subst (λ v → ValR gb (LOps.injB bCod v) (SD.fromB σ′ b (Model.valueᵐ mo M (SD.toB σ′ a y))))
          (sym (trans (read-value M (_ ∈K? valueKeys (toISig Σ)) (LOps.prjB bDom x)) (cong (λ z → SI.fromB b (Model.valueᵐ mo M z)) (toB-R σ′ a bDom ga r))))
          (base-R σ′ b bCod gb _)
  sig-t (value a SG.Many b) (LW.con-fun bDom bCod) h mem (g-⇒ ga gb) M {x} {y} r =
    subst (λ v → ValR gb (LOps.injB bCod v) (SD.fromB σ′ b (Model.valueᵐ mo M (SD.toB σ′ a y))))
          (sym (trans (read-value M (_ ∈K? valueKeys (toISig Σ)) (LOps.prjB bDom x)) (cong (λ z → SI.fromB b (Model.valueᵐ mo M z)) (toB-R σ′ a bDom ga r))))
          (base-R σ′ b bCod gb _)
  sig-t (value a q b) (LW.con-base ()) h mem gs M
  sig-t (operation a SG.Zero b) k () mem gs M
  sig-t (operation a SG.One b)  k () mem gs M
  sig-t (operation a SG.Many b) (LW.con-fun bDom bCod) h mem (g-⇒ ga gb) M {x} {y} r =
    sig-op M bDom bCod ga gb r (T.isVoid? ⌞ b ⌟) (T.isUnit? ⌞ b ⌟)
  sig-t (operation a SG.Many b) (LW.con-base ()) h mem gs M

  -- From the compiler's declaration to the Spec's.
  sig-w : ∀ {c} t (k : LW.IsConcrete (declTy t)) (h : LH.HonestFFI (declTy t)) (mem : (showCanonical c , declTy t) ∈ toISig Σ)
          {T} (gs : GR (declTy t) (⌜ T ⌝ᵈ ST.⟨ σ′ ⟩)) (M : (c ∶ T) ∈ Σ) → T ≡ t
        → ValR gs (LOps.sigOpRefᵛ fmt (toISig Σ) I c k mem) (SM.sigopᵛ Σ fmt S₀ σ′ c T M mo)
  sig-w t k h mem gs M refl = sig-t t k h mem gs M

  sig-v : ∀ {c A} (k : LW.IsConcrete A) (h : LH.HonestFFI A) (mem : (showCanonical c , A) ∈ toISig Σ)
          {T} (gs : GR A (⌜ T ⌝ᵈ ST.⟨ σ′ ⟩)) (M : (c ∶ T) ∈ Σ) → T ≡ declS A
        → (Σ[ d ∈ Decl ] (d ∈ Σ) × (sname d ≡ showCanonical c) × (declTy (Decl.type d) ≡ A))
        → ValR gs (LOps.sigOpRefᵛ fmt (toISig Σ) I c k mem) (SM.sigopᵛ Σ fmt S₀ σ′ c T M mo)
  sig-v k h mem gs M eT ((_ ∶ t) , _ , _ , refl) = sig-w t k h mem gs M (trans eT (declS-declTy t))

-- The compiler's implementation and the Spec's model agree on every
-- declaration (`Program.SigG`), whichever way the compiler's declarations are
-- matched to Σ's.
sig-G : (sigop-S : ∀ {c A} → WordName c → (showCanonical c , A) ∈ toISig Σ → (c ∶ declS A) ∈ Σ) → PG.SigG Σ sigop-S fmt I mo
sig-G sigop-S S₀ σ′ k h rf wn mem gs = sig-v S₀ σ′ k h mem gs (sigop-S wn mem) refl (mem-view mem)

------------------------------------------------------------------------
-- The calls: answered and observed alike
------------------------------------------------------------------------

private
  answer-there : ∀ {k ks} (ct : Once.Internal.Contract.Contract) → k ∈ ks → k ∈ answer-step ct ks
  answer-there (Once.Internal.Contract.value _)   m = m
  answer-there (Once.Internal.Contract.answers _) m = there m
  answer-there Once.Internal.Contract.effect      m = m

  eff-in : ∀ s A B (dv : Dec (B ≡ T.Void)) (du : Dec (B ≡ T.Unit)) → B ≢ T.Void → B ≢ T.Unit → ∀ ks
         → key s A B ∈ answer-step (Once.Internal.Contract.contract-eff s A B dv du) ks
  eff-in s A B (yes e) du      ¬v ¬u ks = ⊥-elim (¬v e)
  eff-in s A B (no _)  (yes e) ¬v ¬u ks = ⊥-elim (¬u e)
  eff-in s A B (no _)  (no _)  ¬v ¬u ks = here refl

  -- an answering operation's key is one of the signature's
  ans-in : ∀ {Σ′ : Signature} {c a q b} (m : (c ∶ operation a q b) ∈ Σ′) → ⌞ b ⌟ ≢ T.Void → ⌞ b ⌟ ≢ T.Unit
         → key (showCanonical c) ⌞ argAt q a ⌟ ⌞ b ⌟ ∈ answerKeys (toISig Σ′)
  ans-in {(c′ ∶ t) ∷ Σ′} (there m) ¬v ¬u = answer-there (Once.Internal.Contract.contractOf (showCanonical c′) (declTy t)) (ans-in m ¬v ¬u)
  ans-in {(c ∶ operation a SG.Zero b) ∷ Σ′} (here refl) ¬v ¬u = eff-in _ _ _ (T.isVoid? ⌞ b ⌟) (T.isUnit? ⌞ b ⌟) ¬v ¬u _
  ans-in {(c ∶ operation a SG.One b)  ∷ Σ′} (here refl) ¬v ¬u = eff-in _ _ _ (T.isVoid? ⌞ b ⌟) (T.isUnit? ⌞ b ⌟) ¬v ¬u _
  ans-in {(c ∶ operation a SG.Many b) ∷ Σ′} (here refl) ¬v ¬u = eff-in _ _ _ (T.isVoid? ⌞ b ⌟) (T.isUnit? ⌞ b ⌟) ¬v ¬u _

  ι : LTr.Interp
  ι = toInterp Σ wf J

  unit-ans : ∀ {cn a b bA x} (M : (cn ∶ operation a SG.Many b) ∈ Σ) h p (eb : b ≡ S.unit) (u : ⌞ b ⌟ ≡ T.Unit) dk {y}
           → Σ[ v ∈ M.⟦ ⌞ b ⌟ ⟧ ] (LTr.callAnswer-at ι h (LTr.callOp cn ⌞ a ⌟ bA ⌞ b ⌟) x (yes u) dk ≡ just v)
               × (v ≡ SI.fromB b (World.answer w (op M) (map toEvent h) y p))
  unit-ans M h p refl refl dk = tt , refl , refl

  ans-at : ∀ {cn a b bA} (M : (cn ∶ operation a SG.Many b) ∈ Σ) (ne : NotEmpty b) {x y} (ra : SI.toB a x ≡ y) h p
         → notEmpty? b ≡ yes p → (du : Dec (⌞ b ⌟ ≡ T.Unit)) (dk : Dec (key (showCanonical cn) ⌞ a ⌟ ⌞ b ⌟ ∈ answerKeys (toISig Σ)))
         → Σ[ v ∈ M.⟦ ⌞ b ⌟ ⟧ ] (LTr.callAnswer-at ι h (LTr.callOp cn ⌞ a ⌟ bA ⌞ b ⌟) x du dk ≡ just v)
             × (v ≡ SI.fromB b (World.answer w (op M) (map toEvent h) y p))
  ans-at {b = b} {bA} M ne {x} {y} ra h p d (yes u) dk = unit-ans {bA = bA} {x = x} M h p (⌞⌟-unit b u) u dk {y}
  ans-at {a = a} {b} M ne {x} ra h p d (no ¬u) (yes p₁) =
    _ , refl , trans (ans-op (ans-G Σ (λ m → m) wf h _ p₁) M refl p d x)
                     (cong (λ z → SI.fromB b (World.answer w (op M) (map toEvent h) z p)) ra)
  ans-at {b = b} M ne ra h p d (no ¬u) (no ¬k) = ⊥-elim (¬k (ans-in M (λ e → ne-void ne (⌞⌟-void b e)) ¬u))

  ev-eq : ∀ {cn} a .(bA : LW.IsBaseType ⌞ a ⌟) {x y} → SI.toB a x ≡ y
        → toEvent (Once.Internal.Event.mk-event cn ⌞ a ⌟ bA x) ≡ S.event cn a y
  ev-eq {cn} a bA {x} ra = cong (λ { (b , v) → S.event cn b v }) (trans (ev-val a bA x) (cong (a ,_) ra))

-- The compiler's interpretation of `J` and `J`'s world agree on every
-- related call (`Observe.Agree`).
agree : Agree ι w
agree = record
  { answered   = λ { (cr {a = a} {b} {bA} M ne) {x} {y} ra h →
                     ne , λ p d → ans-at {bA = bA} M ne ra h p d (T.isUnit? ⌞ b ⌟) (key _ ⌞ a ⌟ ⌞ b ⌟ ∈K? answerKeys (toISig Σ)) }
  ; call-event = λ { (cr {a = a} M ne) ra → ev-eq a _ ra }
  ; halt-event = λ { (hr {a = a} M) ra → ev-eq a _ ra }
  ; halt-void  = λ { (hr M) () }
  }
