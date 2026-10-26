{-# OPTIONS --guardedness #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.SpecSig — a Spec Interpretation, read as the compiler's,
-- agrees with itself (plan 0.121 §3.5; plan 0.122 §5.5: against the Spec's
-- own meaning, over `SpecRun`).
--
-- `SpecInterp` reads a Spec Interpretation `J` of Σ as the compiler's: an
-- implementation of `toISig Σ` (`toImpl`) and so an interpretation
-- (`toInterp`). Against it, a reference to a declaration of Σ — the Spec's
-- meaning: the world's model, or the Spec's call — is related to the source
-- semantics' contract computation (`sig-SD`), and the calls are answered and
-- observed as the Spec's (`agree`, the hypothesis of
-- `SpecObserve.observe-R`).
--
-- The compiler finds a declaration by its RENDERED name (`showCanonical`); the
-- reading is the declaration's when no two of Σ's declarations render alike
-- (`uniq`). Each reading of `toImpl` is first described by the declaration it
-- comes from (`PureG`, `AnsG`), then pinned to it by that uniqueness.
------------------------------------------------------------------------

open import Data.List using (List; map)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
open import Once.Name using (showCanonical; WordName)
open import Once.Spec.Numerics using (TargetNum)
open import Once.Spec.Signature using (Signature; WellFormed; Decl)
open import Once.Spec.Type using (TySub)
import Once.Spec.Observation as Obs

module Once.Adequacy.SpecSig
  (Σ : Signature) (wf : WellFormed Σ) (J : Obs.Interp Σ)
  (uniq : Unique (map (λ d → showCanonical (Decl.name d)) Σ)) (fmt : TargetNum) (σ₀ : TySub 0 0) where

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
import Once.Type.Core as T
import Once.Spec.Type as T
import Once.Spec.Grade as G
import Once.Type.Concrete as LW
import Once.Spec.Type as LW
import Once.Internal.Trace as LTr
open import Once.Internal.Event using (SigOpEvent; toEvent; baseOf; valOf)
open import Once.Contract using (Key; key; kname; kdom; kcod; valueKeys; answerKeys; value-step; answer-step; valueOf; valueOf-at; _∈K?_; Impl)
open import Once.ContractLaws using (value-∈; base-contract)
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
open SI using (declTy; ⌞_⌟; qL; toImpl; toInterp)
open import Once.Core.Decl using (toISig; ∈-toISig; ⌜⌝ᵈ-concrete; ⌜⌝-base; declS; ⌜declS⌝)
open import Once.Type.Honest using (HonestFFI)
open import Once.Weaken using (wk₀-id)
open import Once.Functor.Translate using (IsConcrete-irrelevant)
open import Once.Denotation.SpecDomain Σ σ₀ using (⟦wk₀⟧ᵛ)
open import Relation.Binary.PropositionalEquality using (subst-∘; subst-subst)
open import Once.Adequacy.SpecRun Σ using (CallR; cr; HaltR; hr; argR; ansR; RunR; BlockR; ret; call; halt; SumR; left; right; return∞-R)
open RunR using (forceR)
open import Once.Adequacy.SpecObserve Σ using (Agree)
open import Once.Adequacy.GradedRelation Σ σ₀ using (RelGV; RelGM)
open import Once.Denotation.ValueDomain using (⟦_⟧ᴰ; injectᵇ; forgetᵇ)
open import Once.Denotation.ValueRel using (RelD; base-eq; base-refl)
open import Once.Denotation.TraceMonadInfLaws using (RelS; RelS-embed)
open import Once.Denotation.TraceMonadLaws using (RelT′-refl)
open import Once.Internal.Iterative using (embed; return∞)
import Once.Denotation.SourceDenote as SDn
open import Once.Denotation.DenotTrace using (sigOpT; module CallEnv)
open import Once.Arith.SigOp.Builders using (value-info; arrow-info; arrow-sem-eff)
open import Once.SigOp.Info using (mk-info')

private
  SD⟦⟧ : T.Type → Set
  SD⟦⟧ X = SD.⟦ X ST.⟨ σ₀ ⟩ ⟧ᵛ

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

base-of : ∀ b .(ib : (LW.Base LW.∅ₖ) ⌞ b ⌟) → baseOf ⌞ b ⌟ ib ≡ b
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

ev-val : ∀ a .(ib : (LW.Base LW.∅ₖ) ⌞ a ⌟) (x : M.⟦ ⌞ a ⌟ ⟧)
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
ans-op : ∀ {h k f} → AnsG h k f → ∀ {c a q b} (m : (c ∶ operation a q b) ∈ Σ) (e : k ≡ key (showCanonical c) ⌞ argAt q a ⌟ ⌞ b ⌟)
       → ∀ p → notEmpty? b ≡ yes p → ∀ x
       → subst Fn e f x ≡ SI.fromB b (World.answer w (op m) (map toEvent h) (SI.toB (argAt q a) x) p)
ans-op {h} (ag m′ ne) m e p d x = ao (one-decl uniq m′ m (cong kname e)) e x p d
  where
    ao : ∀ {c c′ a a′ q q′ b b′} {m : (c ∶ operation a q b) ∈ Σ} {m′ : (c′ ∶ operation a′ q′ b′) ∈ Σ} {ne : NotEmpty b′}
       → _≡_ {A = Σ[ d ∈ Decl ] d ∈ Σ} ((c′ ∶ operation a′ q′ b′) , m′) ((c ∶ operation a q b) , m)
       → (e : key (showCanonical c′) ⌞ argAt q′ a′ ⌟ ⌞ b′ ⌟ ≡ key (showCanonical c) ⌞ argAt q a ⌟ ⌞ b ⌟) → ∀ x p
       → notEmpty? b ≡ yes p
       → subst Fn e (λ x → SI.fromB b′ (SI.answerAt-dec Σ J (op m′) (map toEvent h) (SI.toB (argAt q′ a′) x) (notEmpty? b′) ne)) x
         ≡ SI.fromB b (World.answer w (op m) (map toEvent h) (SI.toB (argAt q a) x) p)
    ao {a = a} {q = q} {b = b} {m = m} {ne = ne} refl refl x p d′ =
      cong (λ dd → SI.fromB b (SI.answerAt-dec Σ J (op m) (map toEvent h) (SI.toB (argAt q a) x) dd ne)) d′

private
  -- a constant's type is a base type
  const-k : ∀ b (k : LW.IsConcrete ⌞ b ⌟) → Σ[ ib ∈ (LW.Base LW.∅ₖ) ⌞ b ⌟ ] (k ≡ LW.con-base ib)
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

------------------------------------------------------------------------
-- Base values: the Spec's against the implementation's
------------------------------------------------------------------------

fromB-R : ∀ b (v : S.⟦ b ⟧ᵇ) → RelGV (S.⌜ b ⌝) (SD.fromB σ₀ b v) (injectᵇ (⌜⌝-base b) (SI.fromB b v))
fromB-R S.unit  v = tt
fromB-R S.void  ()
fromB-R S.int   v = refl
fromB-R S.float v = refl
fromB-R (a S.* b) (x , y)  = fromB-R a x , fromB-R b y
fromB-R (a S.+ b) (inj₁ x) = fromB-R a x
fromB-R (a S.+ b) (inj₂ y) = fromB-R b y

toB-R : ∀ b {x y} → RelGV (S.⌜ b ⌝) x y → SI.toB b (forgetᵇ (⌜⌝-base b) y) ≡ SD.toB σ₀ b x
toB-R S.unit  r = refl
toB-R S.void  {()}
toB-R S.int   r = sym r
toB-R S.float r = sym r
toB-R (a S.* b) {_ , _} {_ , _} (r , r′) = cong₂ _,_ (toB-R a r) (toB-R b r′)
toB-R (a S.+ b) {inj₁ _} {inj₁ _} r = cong inj₁ (toB-R a r)
toB-R (a S.+ b) {inj₂ _} {inj₂ _} r = cong inj₂ (toB-R b r)

-- The implementation's closures over first-order values are related to
-- themselves.
private
  emb-self : ∀ {C} (bC : (LW.Base LW.∅ₖ) C) (t : LTr.T M.⟦ C ⟧) → RelS (RelD C) (embed (LTr.fmapT (injectᵇ bC) t)) (embed (LTr.fmapT (injectᵇ bC) t))
  emb-self bC t = RelS-embed (RelT′-refl (base-refl bC) (LTr.fmapT (injectᵇ bC) t))

  ptr-self : ∀ {Dom Cod} (bDom : (LW.Base LW.∅ₖ) Dom) (bCod : (LW.Base LW.∅ₖ) Cod) (f : M.⟦ Dom ⟧ → LTr.T M.⟦ Cod ⟧)
               {a a′ : ⟦ Dom ⟧ᴰ} → RelD Dom a a′
           → RelS (RelD Cod) (embed (LTr.fmapT (injectᵇ bCod) (f (forgetᵇ bDom a)))) (embed (LTr.fmapT (injectᵇ bCod) (f (forgetᵇ bDom a′))))
  ptr-self bDom bCod f {a} r with base-eq bDom r
  ... | refl = emb-self bCod (f (forgetᵇ bDom a))

------------------------------------------------------------------------
-- The declarations: the Spec's reference against the source's contract
------------------------------------------------------------------------

private
  ι′ : LTr.Interp
  ι′ = toInterp Σ wf J

-- A value read from the world's pure half, at a key the signature provides.
val-R : ∀ (ψ : LTr.FFIAnswers) → ψ ≡ LTr.pureHalf ι′ → ∀ {D : T.Type} (c : _) b (x : M.⟦ D ⟧) (v : S.⟦ b ⟧ᵇ)
      → key (showCanonical c) D ⌞ b ⌟ ∈ valueKeys (toISig Σ)
      → (∀ p₀ → LTr.pure ι′ (key (showCanonical c) D ⌞ b ⌟) p₀ x ≡ SI.fromB b v)
      → RelGM G.pure (S.⌜ b ⌝) (SD.fromB σ₀ b v) (embed (LTr.fmapT (injectᵇ (⌜⌝-base b)) (LTr.resT (ψ c D ⌞ b ⌟ x))))
val-R ψ refl {D} c b x v p h = go (key (showCanonical c) D ⌞ b ⌟ ∈K? valueKeys (toISig Σ))
  where
    go : (d : Dec (key (showCanonical c) D ⌞ b ⌟ ∈ valueKeys (toISig Σ)))
       → RelGM G.pure (S.⌜ b ⌝) (SD.fromB σ₀ b v)
               (embed (LTr.fmapT (injectᵇ (⌜⌝-base b)) (LTr.resT (LTr.pureHalf-at ι′ (key (showCanonical c) D ⌞ b ⌟) d x))))
    forceR (go (yes p₀)) = ret (left (subst (λ z → RelGV (S.⌜ b ⌝) (SD.fromB σ₀ b v) (injectᵇ (⌜⌝-base b) z)) (sym (h p₀)) (fromB-R b v)))
    go (no ¬p) = ⊥-elim (¬p p)

module _ {s₀} (S₀ : SC.Defs s₀) (σ : SDn.DefsSem) (eψ : CallEnv.ffiE (SDn.DefsSem.calls σ) ≡ LTr.pureHalf ι′) where

  private
    ψ = CallEnv.ffiE (SDn.DefsSem.calls σ)

    -- an operation's call, by the form its answer type decides
    op-R : ∀ {c a q b} (M : (c ∶ operation a q b) ∈ Σ) (bDom : (LW.Base LW.∅ₖ) ⌞ argAt q a ⌟) {x y}
         → SI.toB (argAt q a) x ≡ y → ∀ dv du
         → RunR (RelGV (S.⌜ b ⌝)) (SE.embed (SE.performT (S.call (op M) y (SD.fromB σ₀ b))))
                (embed (LTr.fmapT (injectᵇ (⌜⌝-base b)) (sigOpT fmt ψ (mk-info' c (arrow-sem-eff dv du) bDom (⌜⌝-base b)) x)))
    forceR (op-R {b = b} M bDom ra (yes e) du) with ⌞⌟-void b e
    ... | refl with e
    ...   | refl = halt (hr M) ra
    forceR (op-R {b = b} M bDom ra (no ¬v) (yes e)) with ⌞⌟-unit b e
    ... | refl with e
    ...   | refl = call (cr M tt) ra (λ {v} {v′} _ → ret (left tt))
    forceR (op-R {b = b} M bDom ra (no ¬v) (no ¬u)) =
      call (cr M (data-ne b (wf-at wf M) ¬v ¬u)) ra
           (λ {v} {v′} e → ret (left (subst (λ z → RelGV (S.⌜ b ⌝) (SD.fromB σ₀ b v) (injectᵇ (⌜⌝-base b) z)) (sym e) (fromB-R b v))))

  -- At each form of declaration.
  sig-SD : ∀ {c} t (M : (c ∶ t) ∈ Σ)
         → RelGM G.pure ⌜ t ⌝ᵈ (SM.sigopᵛ Σ fmt S₀ σ₀ c t M mo) (SDn.sigOpSem ⌜ t ⌝ᵈ c (⌜⌝ᵈ-concrete t) fmt σ)
  sig-SD {c} (constant S.unit) M = val-R ψ eψ c S.unit  tt (Model.constantᵐ mo M) (value-∈ (∈-toISig M) (base-contract (showCanonical c) (⌜⌝-base S.unit)))  (λ p₀ → read-const M {p₀} (yes p₀))
  sig-SD {c} (constant S.void) M = val-R ψ eψ c S.void  tt (Model.constantᵐ mo M) (value-∈ (∈-toISig M) (base-contract (showCanonical c) (⌜⌝-base S.void)))  (λ p₀ → read-const M {p₀} (yes p₀))
  sig-SD {c} (constant S.int) M = val-R ψ eψ c S.int   tt (Model.constantᵐ mo M) (value-∈ (∈-toISig M) (base-contract (showCanonical c) (⌜⌝-base S.int)))   (λ p₀ → read-const M {p₀} (yes p₀))
  sig-SD {c} (constant S.float) M = val-R ψ eψ c S.float tt (Model.constantᵐ mo M) (value-∈ (∈-toISig M) (base-contract (showCanonical c) (⌜⌝-base S.float))) (λ p₀ → read-const M {p₀} (yes p₀))
  sig-SD {c} (constant (a S.* b)) M = val-R ψ eψ c (a S.* b) tt (Model.constantᵐ mo M) (value-∈ (∈-toISig M) (base-contract (showCanonical c) (⌜⌝-base (a S.* b)))) (λ p₀ → read-const M {p₀} (yes p₀))
  sig-SD {c} (constant (a S.+ b)) M = val-R ψ eψ c (a S.+ b) tt (Model.constantᵐ mo M) (value-∈ (∈-toISig M) (base-contract (showCanonical c) (⌜⌝-base (a S.+ b)))) (λ p₀ → read-const M {p₀} (yes p₀))
  sig-SD {c} (value a SG.Zero b) M =
    return∞-R ( val-R ψ eψ c b tt (Model.valueᵐ mo M tt) (value-∈ (∈-toISig M) refl) (λ p₀ → read-value M {p₀} (yes p₀) tt)
              , emb-self (⌜⌝-base b) (LTr.resT (ψ c LW.Unit ⌞ b ⌟ tt)) )
  sig-SD {c} (value a SG.One b) M =
    return∞-R ( (λ {x} {y} r → val-R ψ eψ c b (forgetᵇ (⌜⌝-base a) y) (Model.valueᵐ mo M (SD.toB σ₀ a x)) (value-∈ (∈-toISig M) refl)
                                 (λ p₀ → trans (read-value M {p₀} (yes p₀) (forgetᵇ (⌜⌝-base a) y))
                                               (cong (λ z → SI.fromB b (Model.valueᵐ mo M z)) (toB-R a r))))
              , ptr-self (⌜⌝-base a) (⌜⌝-base b) (λ x → sigOpT fmt ψ (arrow-info (G.mk-kind SG.One G.pure) c (⌜⌝-base a) (⌜⌝-base b)) x) )
  sig-SD {c} (value a SG.Many b) M =
    return∞-R ( (λ {x} {y} r → val-R ψ eψ c b (forgetᵇ (⌜⌝-base a) y) (Model.valueᵐ mo M (SD.toB σ₀ a x)) (value-∈ (∈-toISig M) refl)
                                 (λ p₀ → trans (read-value M {p₀} (yes p₀) (forgetᵇ (⌜⌝-base a) y))
                                               (cong (λ z → SI.fromB b (Model.valueᵐ mo M z)) (toB-R a r))))
              , ptr-self (⌜⌝-base a) (⌜⌝-base b) (λ x → sigOpT fmt ψ (arrow-info (G.mk-kind SG.Many G.pure) c (⌜⌝-base a) (⌜⌝-base b)) x) )
  sig-SD {c} (operation a SG.Zero b) M =
    return∞-R ( op-R M LW.b-Unit refl (T.isVoid? ⌞ b ⌟) (T.isUnit? ⌞ b ⌟)
              , emb-self (⌜⌝-base b) (sigOpT fmt ψ (arrow-info (G.mk-kind SG.Zero G.act) c LW.b-Unit (⌜⌝-base b)) tt) )
  sig-SD {c} (operation a SG.One b) M =
    return∞-R ( (λ {x} {y} r → op-R M (⌜⌝-base a) (toB-R a r) (T.isVoid? ⌞ b ⌟) (T.isUnit? ⌞ b ⌟))
              , ptr-self (⌜⌝-base a) (⌜⌝-base b) (λ x → sigOpT fmt ψ (arrow-info (G.mk-kind SG.One G.act) c (⌜⌝-base a) (⌜⌝-base b)) x) )
  sig-SD {c} (operation a SG.Many b) M =
    return∞-R ( (λ {x} {y} r → op-R M (⌜⌝-base a) (toB-R a r) (T.isVoid? ⌞ b ⌟) (T.isUnit? ⌞ b ⌟))
              , ptr-self (⌜⌝-base a) (⌜⌝-base b) (λ x → sigOpT fmt ψ (arrow-info (G.mk-kind SG.Many G.act) c (⌜⌝-base a) (⌜⌝-base b)) x) )

  -- …and at the type the surface reads the declaration at: its honest FFI
  -- type, through the declaration's code (`⌜declS⌝`) and the ground index
  -- (`wk₀`).
  private
    at-type : ∀ {X Y : T.Type} (e : X ≡ Y) {c} (kX : LW.IsConcrete X) (kY : LW.IsConcrete Y) {v}
            → RelGM G.pure X v (SDn.sigOpSem X c kX fmt σ)
            → RelGM G.pure Y (subst SD⟦⟧ e v) (SDn.sigOpSem Y c kY fmt σ)
    at-type refl kX kY r rewrite IsConcrete-irrelevant kX kY = r

  sig-rel : ∀ {T : T.Type} (k : LW.IsConcrete T) (h : HonestFFI T) {c} (M : (c ∶ declS T) ∈ Σ)
          → RelGM G.pure T (subst (λ X → X) (⟦wk₀⟧ᵛ T) (subst SD⟦⟧ (⌜declS⌝ k h) (SM.sigopᵛ Σ fmt S₀ σ₀ c (declS T) M mo)))
                           (SDn.sigOpSem T c k fmt σ)
  sig-rel {T} k h {c} M =
    subst (λ z → RelGM G.pure T z (SDn.sigOpSem T c k fmt σ))
          (sym (trans (sym (subst-∘ {P = λ (X : Set) → X} {f = SD⟦⟧} (wk₀-id T)))
                      (subst-subst {P = SD⟦⟧} (⌜declS⌝ k h) {y≡z = wk₀-id T})))
          (at-type (trans (⌜declS⌝ k h) (wk₀-id T)) (⌜⌝ᵈ-concrete (declS T)) k (sig-SD (declS T) M))

------------------------------------------------------------------------
-- The calls: answered and observed alike
------------------------------------------------------------------------

private
  answer-there : ∀ {k ks} (ct : Once.Contract.Contract) → k ∈ ks → k ∈ answer-step ct ks
  answer-there (Once.Contract.value _)   m = m
  answer-there (Once.Contract.answers _) m = there m
  answer-there Once.Contract.effect      m = m

  eff-in : ∀ s A B (dv : Dec (B ≡ T.Void)) (du : Dec (B ≡ T.Unit)) → B ≢ T.Void → B ≢ T.Unit → ∀ ks
         → key s A B ∈ answer-step (Once.Contract.contract-eff s A B dv du) ks
  eff-in s A B (yes e) du      ¬v ¬u ks = ⊥-elim (¬v e)
  eff-in s A B (no _)  (yes e) ¬v ¬u ks = ⊥-elim (¬u e)
  eff-in s A B (no _)  (no _)  ¬v ¬u ks = here refl

  -- an answering operation's key is one of the signature's
  ans-in : ∀ {Σ′ : Signature} {c a q b} (m : (c ∶ operation a q b) ∈ Σ′) → ⌞ b ⌟ ≢ T.Void → ⌞ b ⌟ ≢ T.Unit
         → key (showCanonical c) ⌞ argAt q a ⌟ ⌞ b ⌟ ∈ answerKeys (toISig Σ′)
  ans-in {(c′ ∶ t) ∷ Σ′} (there m) ¬v ¬u = answer-there (Once.Contract.contractOf (showCanonical c′) (declTy t)) (ans-in m ¬v ¬u)
  ans-in {(c ∶ operation a SG.Zero b) ∷ Σ′} (here refl) ¬v ¬u = eff-in _ _ _ (T.isVoid? ⌞ b ⌟) (T.isUnit? ⌞ b ⌟) ¬v ¬u _
  ans-in {(c ∶ operation a SG.One b)  ∷ Σ′} (here refl) ¬v ¬u = eff-in _ _ _ (T.isVoid? ⌞ b ⌟) (T.isUnit? ⌞ b ⌟) ¬v ¬u _
  ans-in {(c ∶ operation a SG.Many b) ∷ Σ′} (here refl) ¬v ¬u = eff-in _ _ _ (T.isVoid? ⌞ b ⌟) (T.isUnit? ⌞ b ⌟) ¬v ¬u _

  ι : LTr.Interp
  ι = toInterp Σ wf J

  unit-ans : ∀ {cn a q b bA x} (M : (cn ∶ operation a q b) ∈ Σ) h p (eb : b ≡ S.unit) (u : ⌞ b ⌟ ≡ T.Unit) dk {y}
           → Σ[ v ∈ M.⟦ ⌞ b ⌟ ⟧ ] (LTr.callAnswer-at ι h (LTr.callOp cn ⌞ argAt q a ⌟ bA ⌞ b ⌟) x (yes u) dk ≡ just v)
               × (v ≡ SI.fromB b (World.answer w (op M) (map toEvent h) y p))
  unit-ans M h p refl refl dk = tt , refl , refl

  ans-at : ∀ {cn a q b bA} (M : (cn ∶ operation a q b) ∈ Σ) (ne : NotEmpty b) {x y} (ra : SI.toB (argAt q a) x ≡ y) h p
         → notEmpty? b ≡ yes p → (du : Dec (⌞ b ⌟ ≡ T.Unit)) (dk : Dec (key (showCanonical cn) ⌞ argAt q a ⌟ ⌞ b ⌟ ∈ answerKeys (toISig Σ)))
         → Σ[ v ∈ M.⟦ ⌞ b ⌟ ⟧ ] (LTr.callAnswer-at ι h (LTr.callOp cn ⌞ argAt q a ⌟ bA ⌞ b ⌟) x du dk ≡ just v)
             × (v ≡ SI.fromB b (World.answer w (op M) (map toEvent h) y p))
  ans-at {b = b} {bA} M ne {x} {y} ra h p d (yes u) dk = unit-ans {bA = bA} {x = x} M h p (⌞⌟-unit b u) u dk {y}
  ans-at {a = a} {b = b} M ne {x} ra h p d (no ¬u) (yes p₁) =
    _ , refl , trans (ans-op (ans-G Σ (λ m → m) wf h _ p₁) M refl p d x)
                     (cong (λ z → SI.fromB b (World.answer w (op M) (map toEvent h) z p)) ra)
  ans-at {b = b} M ne ra h p d (no ¬u) (no ¬k) = ⊥-elim (¬k (ans-in M (λ e → ne-void ne (⌞⌟-void b e)) ¬u))

  ev-eq : ∀ {cn} a .(bA : (LW.Base LW.∅ₖ) ⌞ a ⌟) {x y} → SI.toB a x ≡ y
        → toEvent (Once.Internal.Event.mk-event cn ⌞ a ⌟ bA x) ≡ S.event cn a y
  ev-eq {cn} a bA {x} ra = cong (λ { (b , v) → S.event cn b v }) (trans (ev-val a bA x) (cong (a ,_) ra))

-- The compiler's interpretation of `J` and `J`'s world agree on every
-- related call (`Observe.Agree`).
agree : Agree ι w
agree = record
  { answered   = λ { (cr {a = a} {q} {b} {bA} M ne) {y} {x} ra h →
                     ne , λ p d → ans-at {bA = bA} M ne ra h p d (T.isUnit? ⌞ b ⌟) (key _ ⌞ argAt q a ⌟ ⌞ b ⌟ ∈K? answerKeys (toISig Σ)) }
  ; call-event = λ { (cr {a = a} {q} M ne) ra → ev-eq (argAt q a) _ ra }
  ; halt-event = λ { (hr {a = a} {q} M) ra → ev-eq (argAt q a) _ ra }
  ; halt-void  = λ { (hr M) () }
  }

