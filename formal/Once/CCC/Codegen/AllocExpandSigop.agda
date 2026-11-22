-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.AllocExpandSigop — a SigOp under the renaming (D468, 3c3b).
--
-- A SigOp reads its argument through Input1 (a register value, or a pointer to
-- its words) and writes its answer at Output's location. A typed read that the
-- primitive run makes succeed reads held cells, and the expanded run's read at
-- the renamed location reads the same value; the answer's words are literals,
-- which the renaming fixes.
------------------------------------------------------------------------

open import Once.CCC.FrameSemantics using (FrameSemantics; fs-numerics; fs-ffi)
open FrameSemantics using (fs-interp)

module Once.CCC.Codegen.AllocExpandSigop {FS : FrameSemantics} where

open import Data.Bool using (Bool; true; false)
open import Data.Maybe using (Maybe; just; nothing)
import Data.Maybe
import Data.List
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Once.Memory.HeapAddress using (HeapLocation; heap-loc; mkHeapRef)
open import Once.CCC.Machine.SMCore
open import Once.CCC.Machine.Locations using (ValueLocation; AtStack; AtDynamic)
open import Once.Spec.Type using (Ty; Unit; Void; Int; Float; _*_; _+_; _⇒[_]_; μ; ν; var)
open import Once.Type using (fits-int; fits-float)
open import Once.Semantics.Machine using (module Value)
open Value using (⟦_⟧)
open import Once.CCC.Codegen.AllocExpandRen {FS} using (ref-of; rhl; rloc; rv)
open import Once.CCC.Codegen.AllocExpandStep {FS} using (module L; rhl-off)
open MemOps {FS} using (readLoc; writeLoc)
open AbstractExec {FS} using (readTyped; readTyped-int; readTyped-float; readTyped-sum; combine-typed; tsize; decode-at)

rloc-off : ∀ ρ (loc : ValueLocation FS) k → rloc ρ (offsetLoc loc k) ≡ offsetLoc (rloc ρ loc) k
rloc-off ρ (AtStack f j)  k = refl
rloc-off ρ (AtDynamic hl) k = cong AtDynamic (rhl-off ρ hl k)

rloc-suc : ∀ ρ (loc : ValueLocation FS) → rloc ρ (sucLoc loc) ≡ sucLoc (rloc ρ loc)
rloc-suc ρ (AtStack f j)                      = refl
rloc-suc ρ (AtDynamic (heap-loc r o))         = refl

module _ (ρ : ℕ → ℕ) (Lv : ℕ → Set) (inj : ∀ r r′ → Lv r → Lv r′ → ρ r ≡ ρ r′ → r ≡ r′)
         {s t : LocState FS} (R : L.LRel ρ Lv inj s t) where

  -- a cell holding a value, at its renamed location
  cell-rel : ∀ loc v → readLoc s loc ≡ just v → readLoc t (rloc ρ loc) ≡ just (rv ρ v)
  cell-rel (AtStack f k)  v e = trans (L.LRel.l-stack R f k) (cong (Data.Maybe.map (rv ρ)) e)
  cell-rel (AtDynamic hl) v e = L.LRel.l-heap R hl v (L.LRel.l-live R hl v e) e

  private
    int-inv : ∀ mv {a} → readTyped-int mv ≡ just a → mv ≡ just (SV-Lit fits-int a)
    int-inv (just (SV-Lit fits-int v)) refl = refl
    int-inv (just (SV-Lit fits-float _)) ()
    int-inv (just (SV-Ptr _)) ()
    int-inv (just (SV-Tag _)) ()
    int-inv (just (SV-Code _)) ()
    int-inv nothing ()

    float-inv : ∀ mv {a} → readTyped-float mv ≡ just a → mv ≡ just (SV-Lit fits-float a)
    float-inv (just (SV-Lit fits-float v)) refl = refl
    float-inv (just (SV-Lit fits-int _)) ()
    float-inv (just (SV-Ptr _)) ()
    float-inv (just (SV-Tag _)) ()
    float-inv (just (SV-Code _)) ()
    float-inv nothing ()

    pair-inv : ∀ {A B : Ty 0} (ma : Maybe ⟦ A ⟧) (mb : Maybe ⟦ B ⟧) {p} → combine-typed ma mb ≡ just p
             → (ma ≡ just (proj₁ p)) × (mb ≡ just (proj₂ p))
    pair-inv (just a) (just b) refl = refl , refl
    pair-inv (just a) nothing ()
    pair-inv nothing  _       ()

  -- ★ a typed read the primitive makes succeed, at the renamed location
  read-rel : ∀ (A : Ty 0) loc {a} → readTyped A loc s ≡ just a → readTyped A (rloc ρ loc) t ≡ just a
  read-rel Unit loc e = e
  read-rel Int loc e =
    trans (cong readTyped-int (cell-rel loc _ (int-inv (readLoc s loc) e))) refl
  read-rel Float loc e =
    trans (cong readTyped-float (cell-rel loc _ (float-inv (readLoc s loc) e))) refl
  read-rel (A * B) loc {a , b} e =
    trans (cong₂′ (read-rel A loc (proj₁ inv))
                  (trans (cong (λ l → readTyped B l t) (sym (rloc-off ρ loc (tsize A)))) (read-rel B (offsetLoc loc (tsize A)) (proj₂ inv))))
          refl
    where
      inv = pair-inv (readTyped A loc s) (readTyped B (offsetLoc loc (tsize A)) s) e
      cong₂′ : ∀ {ma mb} → ma ≡ just a → mb ≡ just b → combine-typed {A} {B} ma mb ≡ just (a , b)
      cong₂′ refl refl = refl
  read-rel (A + B) loc {x} e = sum (readLoc s loc) refl e
    where
      sl = sucLoc loc
      sum : ∀ mt → readLoc s loc ≡ mt
          → readTyped-sum (λ _ → readTyped A sl s) (λ _ → readTyped B sl s) mt (readLoc s sl) ≡ just x
          → readTyped-sum (λ _ → readTyped A (sucLoc (rloc ρ loc)) t) (λ _ → readTyped B (sucLoc (rloc ρ loc)) t)
                          (readLoc t (rloc ρ loc)) (readLoc t (sucLoc (rloc ρ loc))) ≡ just x
      sum (just (SV-Tag zero)) et e′ =
        trans (cong (λ m → readTyped-sum (λ _ → readTyped A (sucLoc (rloc ρ loc)) t) (λ _ → readTyped B (sucLoc (rloc ρ loc)) t) m (readLoc t (sucLoc (rloc ρ loc))))
                    (cell-rel loc (SV-Tag zero) et))
              (inl-of (readTyped A sl s) refl e′)
        where
          inl-of : ∀ ma → readTyped A sl s ≡ ma → Data.Maybe.map inj₁ ma ≡ just x
                 → Data.Maybe.map inj₁ (readTyped A (sucLoc (rloc ρ loc)) t) ≡ just x
          inl-of (just a) ea refl = cong (Data.Maybe.map inj₁) (trans (cong (λ l → readTyped A l t) (sym (rloc-suc ρ loc))) (read-rel A sl ea))
          inl-of nothing  ea ()
      sum (just (SV-Tag (suc zero))) et e′ =
        trans (cong (λ m → readTyped-sum (λ _ → readTyped A (sucLoc (rloc ρ loc)) t) (λ _ → readTyped B (sucLoc (rloc ρ loc)) t) m (readLoc t (sucLoc (rloc ρ loc))))
                    (cell-rel loc (SV-Tag (suc zero)) et))
              (inr-of (readTyped B sl s) refl e′)
        where
          inr-of : ∀ mb → readTyped B sl s ≡ mb → Data.Maybe.map inj₂ mb ≡ just x
                 → Data.Maybe.map inj₂ (readTyped B (sucLoc (rloc ρ loc)) t) ≡ just x
          inr-of (just b) eb refl = cong (Data.Maybe.map inj₂) (trans (cong (λ l → readTyped B l t) (sym (rloc-suc ρ loc))) (read-rel B sl eb))
          inr-of nothing  eb ()
      sum (just (SV-Tag (suc (suc _)))) et ()
      sum (just (SV-Ptr _)) et ()
      sum (just (SV-Lit _ _)) et ()
      sum (just (SV-Code _)) et ()
      sum nothing et ()
  read-rel Void loc ()
  read-rel (_ ⇒[ _ ] _) loc ()
  read-rel (μ _) loc ()
  read-rel (ν _ _) loc ()


  open import Once.Spec.Type using (Base; b-var; b-Unit; b-Void; b-Int; b-Float; b-*; b-+; ∅ₖ)

  -- ★ the argument the primitive decodes, decoded alike from the renamed register
  decode-rel : ∀ {A} (b : Base ∅ₖ A) v {a} → decode-at b v s ≡ just a → decode-at b (rv ρ v) t ≡ just a
  decode-rel b-Unit  v e = e
  decode-rel b-Int   (SV-Lit fits-int _)   e = e
  decode-rel b-Int   (SV-Lit fits-float _) ()
  decode-rel b-Int   (SV-Ptr _) ()
  decode-rel b-Int   (SV-Tag _) ()
  decode-rel b-Int   (SV-Code _) ()
  decode-rel b-Float (SV-Lit fits-float _) e = e
  decode-rel b-Float (SV-Lit fits-int _) ()
  decode-rel b-Float (SV-Ptr _) ()
  decode-rel b-Float (SV-Tag _) ()
  decode-rel b-Float (SV-Code _) ()
  decode-rel {A} (b-* _ _) (SV-Ptr loc) e = read-rel A loc e
  decode-rel (b-* _ _) (SV-Lit _ _) ()
  decode-rel (b-* _ _) (SV-Tag _) ()
  decode-rel (b-* _ _) (SV-Code _) ()
  decode-rel {A} (b-+ _ _) (SV-Ptr loc) e = read-rel A loc e
  decode-rel (b-+ _ _) (SV-Lit _ _) ()
  decode-rel (b-+ _ _) (SV-Tag _) ()
  decode-rel (b-+ _ _) (SV-Code _) ()
  decode-rel b-Void v ()

  ------------------------------------------------------------------------
  -- The answer's words: literals and tags, written in a frame
  ------------------------------------------------------------------------

open AbstractExec {FS} using (writeTyped; writeZeros; zero-word)

module Words (ρ : ℕ → ℕ) (Lv : ℕ → Set) (inj : ∀ r r′ → Lv r → Lv r′ → ρ r ≡ ρ r′ → r ≡ r′) where
  import Data.Nat as ℕ

  zeros-rel : ∀ {s t} n f k → L.LRel ρ Lv inj s t → L.LRel ρ Lv inj (writeZeros n (AtStack f k) s) (writeZeros n (AtStack f k) t)
  zeros-rel zero    f k R = R
  zeros-rel (suc n) f k R = zeros-rel n f (suc k) (L.lrel-stack-write ρ Lv inj f k zero-word R)

  -- ★ the answer written at a frame's slots, on both sides
  write-rel : ∀ {s t} (B : Ty 0) v f k → L.LRel ρ Lv inj s t → L.LRel ρ Lv inj (writeTyped B v (AtStack f k) s) (writeTyped B v (AtStack f k) t)
  write-rel Unit    v f k R = R
  write-rel Int     v f k R = L.lrel-stack-write ρ Lv inj f k (SV-Lit fits-int v) R
  write-rel Float   v f k R = L.lrel-stack-write ρ Lv inj f k (SV-Lit fits-float v) R
  write-rel (A * B) (a , b) f k R = write-rel B b f (tsize A ℕ.+ k) (write-rel A a f k R)
  write-rel (A + B) (inj₁ a) f k R =
    zeros-rel ((tsize A ℕ.⊔ tsize B) ℕ.∸ tsize A) f (suc (tsize A) ℕ.+ k)
      (write-rel A a f (suc k) (L.lrel-stack-write ρ Lv inj f k (SV-Tag 0) R))
  write-rel (A + B) (inj₂ b) f k R =
    zeros-rel ((tsize A ℕ.⊔ tsize B) ℕ.∸ tsize B) f (suc (tsize B) ℕ.+ k)
      (write-rel B b f (suc k) (L.lrel-stack-write ρ Lv inj f k (SV-Tag 1) R))
  write-rel Void v f k R = R
  write-rel (_ ⇒[ _ ] _) v f k R = R
  write-rel (μ _) v f k R = R
  write-rel (ν _ _) v f k R = R

  -- an answer of no words writes nothing
  write-none : ∀ (B : Ty 0) v loc (s : LocState FS) → tsize B ≡ 0 → writeTyped B v loc s ≡ s
  write-none Unit    v loc s _ = refl
  write-none Void    v loc s _ = refl
  write-none (A * B) (a , b) loc s e =
    trans (write-none B b (offsetLoc loc (tsize A)) (writeTyped A a loc s) (Data.Nat.Properties.m+n≡0⇒n≡0 (tsize A) e))
          (write-none A a loc s (Data.Nat.Properties.m+n≡0⇒m≡0 (tsize A) e))
    where import Data.Nat.Properties
  write-none Int     v loc s ()
  write-none Float   v loc s ()
  write-none (A + B) v loc s ()
  write-none (_ ⇒[ _ ] _) v loc s ()
  write-none (μ _) v loc s ()
  write-none (ν _ _) v loc s ()

------------------------------------------------------------------------
-- The gates and the register's kind under the renaming
------------------------------------------------------------------------

open ExecFinal {FS} using (range-ok; ans-ok)

range-rv : ∀ ρ fr n v → range-ok fr n (rv ρ v) ≡ range-ok fr n v
range-rv ρ fr zero    v = refl
range-rv ρ fr (suc n) (SV-Ptr (AtStack _ _)) = refl
range-rv ρ fr (suc n) (SV-Ptr (AtDynamic _)) = refl
range-rv ρ fr (suc n) (SV-Lit _ _) = refl
range-rv ρ fr (suc n) (SV-Tag _) = refl
range-rv ρ fr (suc n) (SV-Code _) = refl

ans-rv : ∀ ρ fr n v → ans-ok fr n (rv ρ v) ≡ ans-ok fr n v
ans-rv ρ fr zero    v = refl
ans-rv ρ fr (suc n) (SV-Ptr (AtStack _ _)) = refl
ans-rv ρ fr (suc n) (SV-Ptr (AtDynamic _)) = refl
ans-rv ρ fr (suc n) (SV-Lit _ _) = refl
ans-rv ρ fr (suc n) (SV-Tag _) = refl
ans-rv ρ fr (suc n) (SV-Code _) = refl

-- a value that is no pointer is its own renaming
rv-nonptr : ∀ ρ v → sv-as-loc v ≡ nothing → rv ρ v ≡ v
rv-nonptr ρ (SV-Ptr _) ()
rv-nonptr ρ (SV-Tag _) _ = refl
rv-nonptr ρ (SV-Lit _ _) _ = refl
rv-nonptr ρ (SV-Code _) _ = refl

as-loc-rv : ∀ ρ v → sv-as-loc (rv ρ v) ≡ Data.Maybe.map (rloc ρ) (sv-as-loc v)
as-loc-rv ρ (SV-Ptr _) = refl
as-loc-rv ρ (SV-Tag _) = refl
as-loc-rv ρ (SV-Lit _ _) = refl
as-loc-rv ρ (SV-Code _) = refl

-- a heap pointer passes the answer's gate only for no words
ans-heap : ∀ fr n hl → ans-ok fr n (SV-Ptr (AtDynamic hl)) ≡ true → n ≡ 0
ans-heap fr zero    hl _ = refl
ans-heap fr (suc n) hl ()

------------------------------------------------------------------------
-- ★ A SigOp's effects, alike on both sides once its argument decoded
------------------------------------------------------------------------

open import Once.SigOp.Info using (SigOpInfo; effect; EffectShape; Pure; Emits; Halts; Answers; module SigOpInfo)
open import Once.Res using (Res; stopped; returns)
open import Once.IR.Semantics.Trace using (callOp; answer)
open import Once.IR.Semantics.Boundary using (atTarget)
open import Once.Type using (FitsInReg; fits-in-reg?)
open AbstractExec {FS} using (exec-sigop-faults-of; exec-sigop-halts-of; sigop-events-of; sigop-answer-of; exec-sigop-output-of
                             ; unread?; pure-sigop-out-aux; pure-sigop-out-val; res-sv; structured-pure-sigop-output; readReg-typed
                             ; call-sigop-val; call-sigop-ans; call-sigop-ans-at; call-sigop-dec; call-ans-at; pure-ans-at; unit-storedvalue)

module Sig (ρ : ℕ → ℕ) (Lv : ℕ → Set) (inj : ∀ r r′ → Lv r → Lv r′ → ρ r ≡ ρ r′ → r ≡ r′)
           {s t : LocState FS} (R : L.LRel ρ Lv inj s t) {A B} (si : SigOpInfo A B) where
  b = SigOpInfo.baseA si
  v₁ = readReg (LocState.regs s) Input1
  in-t : readReg (LocState.regs t) Input1 ≡ rv ρ v₁
  in-t = L.LRel.l-regs R Input1

  module D {a} (dec : decode-at b v₁ s ≡ just a) where
    dec-t : decode-at b (readReg (LocState.regs t) Input1) t ≡ decode-at b v₁ s
    dec-t = trans (cong (λ v → decode-at b v t) in-t) (trans (decode-rel ρ Lv inj R b v₁ dec) (sym dec))

    faults-eq : ∀ e → exec-sigop-faults-of e si t ≡ exec-sigop-faults-of e si s
    faults-eq Pure      = cong unread? dec-t
    faults-eq (Halts _) = cong unread? dec-t
    faults-eq (Emits _) = cong unread? dec-t
    faults-eq Answers   = cong unread? dec-t

    halts-eq : ∀ e → exec-sigop-halts-of e si t ≡ exec-sigop-halts-of e si s
    halts-eq Pure      = cong unread? dec-t
    halts-eq (Halts _) = refl
    halts-eq (Emits _) = cong unread? dec-t
    halts-eq Answers   = cong unread? dec-t

    events-eq : ∀ e → sigop-events-of e si t ≡ sigop-events-of e si s
    events-eq Pure      = refl
    events-eq (Halts _) = cong (AbstractExec.events-at-arg {FS} si) dec-t
    events-eq (Emits _) = cong (AbstractExec.events-at-arg {FS} si) dec-t
    events-eq Answers   = cong (AbstractExec.events-at-arg {FS} si) dec-t

    -- the interpretation's answer reads the log, the same on both sides
    ans-at-eq : ∀ D m → call-ans-at si t D m ≡ call-ans-at si s D m
    ans-at-eq (Relation.Nullary.yes p) (just a′) = cong (λ L′ → just (atTarget (fs-numerics FS) B
                                                                (answer (fs-interp FS) L′ (callOp (SigOpInfo.name si) A b B) p a′)))
                                                        (L.LRel.l-log R)
    ans-at-eq (Relation.Nullary.yes p) nothing = refl
    ans-at-eq (Relation.Nullary.no _)  m       = refl

    answer-eq : ∀ e → sigop-answer-of e si t ≡ sigop-answer-of e si s
    answer-eq Pure      = cong (pure-ans-at si) dec-t
    answer-eq Answers   = trans (cong (call-ans-at si t (call-sigop-dec si)) dec-t) (ans-at-eq (call-sigop-dec si) _)
    answer-eq (Emits _) = refl
    answer-eq (Halts _) = refl

    -- a pointer argument decoded: its words read alike at the renamed location
    ptr-read : ∀ loc → v₁ ≡ SV-Ptr loc → AbstractExec.readTyped {FS} A (rloc ρ loc) t ≡ AbstractExec.readTyped {FS} A loc s
    ptr-read loc e = by b (subst (λ v → decode-at b v s ≡ just a) e dec)
      where
        by : (b′ : Once.Spec.Type.Base Once.Spec.Type.∅ₖ A) → decode-at b′ (SV-Ptr loc) s ≡ just a
           → AbstractExec.readTyped {FS} A (rloc ρ loc) t ≡ AbstractExec.readTyped {FS} A loc s
        by Once.Spec.Type.b-Unit _ = refl
        by (Once.Spec.Type.b-* _ _) e′ = trans (read-rel ρ Lv inj R A loc e′) (sym e′)
        by (Once.Spec.Type.b-+ _ _) e′ = trans (read-rel ρ Lv inj R A loc e′) (sym e′)
        by Once.Spec.Type.b-Int ()
        by Once.Spec.Type.b-Float ()
        by Once.Spec.Type.b-Void ()

    -- an output word the op computes is a literal (or the register Output)
    out-val-fix : ∀ fitB m → rv ρ (pure-sigop-out-val si fitB m) ≡ pure-sigop-out-val si fitB m
    out-val-fix fitB (just a′) = res-fix (Once.SigOp.Info.semM (fs-ffi FS) si (fs-numerics FS) a′)
      where
        res-fix : ∀ r → rv ρ (res-sv fitB r) ≡ res-sv fitB r
        res-fix (returns _) = refl
        res-fix stopped     = refl
    out-val-fix fitB nothing = refl

    output-eq : ∀ e → exec-sigop-output-of e si t ≡ rv ρ (exec-sigop-output-of e si s)
    output-eq Pure      = pure (fits-in-reg? B)
      where
        pure : ∀ mf → pure-sigop-out-aux si t mf (sv-as-loc (readReg (LocState.regs t) Input1)) ≡ rv ρ (pure-sigop-out-aux si s mf (sv-as-loc v₁))
        pure nothing = trans refl (L.LRel.l-regs R Output)
        pure (just fitB) = trans (cong (pure-sigop-out-aux si t (just fitB)) (trans (cong sv-as-loc in-t) (as-loc-rv ρ v₁)))
                                 (at-kind (sv-as-loc v₁) refl)
          where
            at-kind : ∀ ml → sv-as-loc v₁ ≡ ml → pure-sigop-out-aux si t (just fitB) (Data.Maybe.map (rloc ρ) ml) ≡ rv ρ (pure-sigop-out-aux si s (just fitB) ml)
            at-kind (just loc) e′ = trans (cong (pure-sigop-out-val si fitB) (ptr-read loc (ptr-of v₁ e′)))
                                          (sym (out-val-fix fitB (AbstractExec.readTyped {FS} A loc s)))
              where
                ptr-of : ∀ v → sv-as-loc v ≡ just loc → v ≡ SV-Ptr loc
                ptr-of (SV-Ptr l) refl = refl
                ptr-of (SV-Tag _) ()
                ptr-of (SV-Lit _ _) ()
                ptr-of (SV-Code _) ()
            at-kind nothing e′ = trans (cong (λ v → pure-sigop-out-val si fitB (readReg-typed A v)) (trans in-t (rv-nonptr ρ v₁ e′)))
                                       (sym (out-val-fix fitB (readReg-typed A v₁)))
    output-eq (Emits _) = refl
    output-eq (Halts _) = refl
    output-eq Answers   = call (fits-in-reg? B)
      where
        call : ∀ mf → call-sigop-val si t mf ≡ rv ρ (call-sigop-val si s mf)
        call nothing = L.LRel.l-regs R Output
        call (just fitB) = ans (call-sigop-dec si)
          where
            ans : ∀ D → call-sigop-ans si t fitB D ≡ rv ρ (call-sigop-ans si s fitB D)
            ans (Relation.Nullary.no _) = refl
            ans (Relation.Nullary.yes p) = trans (cong (call-sigop-ans-at si t fitB p) dec-t) (at (decode-at b v₁ s))
              where
                at : ∀ m → call-sigop-ans-at si t fitB p m ≡ rv ρ (call-sigop-ans-at si s fitB p m)
                at (just a′) = cong (λ L′ → SV-Lit fitB (atTarget (fs-numerics FS) B
                                                (answer (fs-interp FS) L′ (callOp (SigOpInfo.name si) A b B) p a′)))
                                    (L.LRel.l-log R)
                at nothing = refl

    ------------------------------------------------------------------------
    -- The answer stored: in a frame word by word, or (a heap pointer) nothing
    ------------------------------------------------------------------------

    open AbstractExec {FS} using (sigop-store; sigop-store-at; sigop-answer; ans-words)

    module W = Words ρ Lv inj

    out-t : readReg (LocState.regs t) Output ≡ rv ρ (readReg (LocState.regs s) Output)
    out-t = L.LRel.l-regs R Output

    store-rel : ∀ fr → ans-ok fr (ans-words B) (readReg (LocState.regs s) Output) ≡ true
              → L.LRel ρ Lv inj (sigop-store si s) (sigop-store si t)
    store-rel fr ok =
      subst₂′ (trans (cong sv-as-loc out-t) (as-loc-rv ρ (readReg (LocState.regs s) Output))) (answer-eq (effect si))
        (by (in-memory? B) refl (sv-as-loc (readReg (LocState.regs s) Output)) refl (sigop-answer si s))
      where
        o = readReg (LocState.regs s) Output
        subst₂′ : ∀ {ml′ ma′} → ml′ ≡ Data.Maybe.map (rloc ρ) (sv-as-loc o) → ma′ ≡ sigop-answer si s
                → L.LRel ρ Lv inj (sigop-store si s) (sigop-store-at {B = B} (in-memory? B) (Data.Maybe.map (rloc ρ) (sv-as-loc o)) (sigop-answer si s) t)
                → L.LRel ρ Lv inj (sigop-store si s) (sigop-store-at {B = B} (in-memory? B) ml′ ma′ t)
        subst₂′ refl refl X = X
        by : ∀ im → in-memory? B ≡ im → ∀ ml → sv-as-loc o ≡ ml → ∀ ma
           → L.LRel ρ Lv inj (sigop-store-at {B = B} im ml ma s) (sigop-store-at {B = B} im (Data.Maybe.map (rloc ρ) ml) ma t)
        by false _ ml _ ma = R
        by true  _ nothing _ ma = R
        by true  _ (just (AtStack f j)) _ (just v) = W.write-rel B v f j R
        by true  _ (just (AtStack f j)) _ nothing  = R
        by true  im (just (AtDynamic hl)) e (just v) =
          Relation.Binary.PropositionalEquality.subst₂ (L.LRel ρ Lv inj)
            (sym (W.write-none B v (AtDynamic hl) s zero-words)) (sym (W.write-none B v (AtDynamic (rhl ρ hl)) t zero-words)) R
          where
            ptr : o ≡ SV-Ptr (AtDynamic hl)
            ptr = ptr-of o e
              where
                ptr-of : ∀ v′ → sv-as-loc v′ ≡ just (AtDynamic hl) → v′ ≡ SV-Ptr (AtDynamic hl)
                ptr-of (SV-Ptr _) refl = refl
                ptr-of (SV-Tag _) ()
                ptr-of (SV-Lit _ _) ()
                ptr-of (SV-Code _) ()
            zero-words : tsize B ≡ 0
            zero-words = trans (sym (cong (λ b′ → Data.Bool.if b′ then tsize B else 0) im))
                               (ans-heap fr (ans-words B) hl (subst (λ v′ → ans-ok fr (ans-words B) v′ ≡ true) ptr ok))
        by true  _ (just (AtDynamic hl)) _ nothing = R

  ------------------------------------------------------------------------
  -- ★ The SigOp's step under the renaming, given it did not fault
  ------------------------------------------------------------------------

  open AbstractExec {FS} using (exec-abstract; exec-sigop-faults; exec-sigop-halts; sigop-events; exec-sigop-output; arg-words; sigop-gate; ans-words)
  open ExecFinal {FS} using (live-frames)
  open import Data.Bool using (_∨_; _∧_; not)

  private
    split∨ : ∀ (a b : Bool) → (a ∨ b) ≡ false → (a ≡ false) × (b ≡ false)
    split∨ false false _ = refl , refl
    not-f : ∀ (a : Bool) → not a ≡ false → a ≡ true
    not-f true _ = refl
    ∧-r : ∀ (a b : Bool) → (a ∧ b) ≡ true → b ≡ true
    ∧-r true b e = e
    unread-f : ∀ {X : Set} (m : Maybe X) → unread? m ≡ false → Σ X λ a → m ≡ just a
    unread-f (just a) _ = a , refl
    unread-f nothing ()

  -- a SigOp that did not fault decoded its argument
  decoded : ∀ e → exec-sigop-faults-of e si s ≡ false → Σ ⟦ A ⟧ λ a → decode-at b v₁ s ≡ just a
  decoded Pure      f = unread-f _ f
  decoded (Halts _) f = unread-f _ f
  decoded (Emits _) f = unread-f _ f
  decoded Answers   f = unread-f _ f

  module E (al al′ : AllocState {FS}) (fr : live-frames al′ ≡ live-frames al)
           (nf : LocState.faulted (proj₁ (exec-abstract (instr-sigop si) s al)) ≡ false) where
    sp = split∨ (exec-sigop-faults si s) _ nf
    dec = proj₂ (decoded (effect si) (proj₁ sp))
    gate-s : sigop-gate al si s ≡ true
    gate-s = not-f _ (proj₁ (split∨ (not (sigop-gate al si s)) _ (proj₂ sp)))
    open D dec

    gate-eq : sigop-gate al′ si t ≡ sigop-gate al si s
    gate-eq = Relation.Binary.PropositionalEquality.cong₂ _∧_
      (trans (Relation.Binary.PropositionalEquality.cong₂ (λ f v → range-ok f (arg-words b) v) fr in-t) (range-rv ρ (live-frames al) (arg-words b) v₁))
      (trans (Relation.Binary.PropositionalEquality.cong₂ (λ f v → ans-ok f (ans-words B) v) fr out-t)
             (ans-rv ρ (live-frames al) (ans-words B) (readReg (LocState.regs s) Output)))

    st-rel = store-rel (live-frames al) (∧-r _ _ gate-s)

    c3 : ∀ {a a′ g g′ f f′ : Bool} → a ≡ a′ → g ≡ g′ → f ≡ f′ → (a ∨ (not g ∨ f)) ≡ (a′ ∨ (not g′ ∨ f′))
    c3 refl refl refl = refl

    step-rel : L.LRel ρ Lv inj (proj₁ (exec-abstract (instr-sigop si) s al)) (proj₁ (exec-abstract (instr-sigop si) t al′))
    step-rel = record
      { l-regs = λ { Input1 → L.LRel.l-regs R Input1 ; Output → output-eq (effect si) }
      ; l-stack = L.LRel.l-stack st-rel
      ; l-heap = L.LRel.l-heap st-rel
      ; l-live = L.LRel.l-live st-rel
      ; l-halt = Relation.Binary.PropositionalEquality.cong₂ (λ h g → h ∨ not g) (halts-eq (effect si)) gate-eq
      ; l-fault = c3 (faults-eq (effect si)) gate-eq (L.LRel.l-fault R)
      ; l-left = L.LRel.l-left R
      ; l-log = Relation.Binary.PropositionalEquality.cong₂ Data.List._++_ (L.LRel.l-log R) (events-eq (effect si)) }

-- an answer stored in a frame, or of no words, leaves the heap
module Heap where
  open AbstractExec {FS} using (sigop-store; sigop-store-at; sigop-answer; ans-words)
  import Data.Nat as ℕ

  zeros-heap : ∀ n f k (x : LocState FS) → LocState.heapMem (writeZeros n (AtStack f k) x) ≡ LocState.heapMem x
  zeros-heap zero    f k x = refl
  zeros-heap (suc n) f k x = zeros-heap n f (suc k) (writeLoc x (AtStack f k) zero-word)

  write-heap : ∀ (B : Ty 0) v f k (x : LocState FS) → LocState.heapMem (writeTyped B v (AtStack f k) x) ≡ LocState.heapMem x
  write-heap Unit    v f k x = refl
  write-heap Int     v f k x = refl
  write-heap Float   v f k x = refl
  write-heap (A * B) (a , b) f k x = trans (write-heap B b f (tsize A ℕ.+ k) (writeTyped A a (AtStack f k) x)) (write-heap A a f k x)
  write-heap (A + B) (inj₁ a) f k x =
    trans (zeros-heap ((tsize A ℕ.⊔ tsize B) ℕ.∸ tsize A) f (suc (tsize A) ℕ.+ k) (writeTyped A a (AtStack f (suc k)) (writeLoc x (AtStack f k) (SV-Tag 0))))
          (write-heap A a f (suc k) (writeLoc x (AtStack f k) (SV-Tag 0)))
  write-heap (A + B) (inj₂ b) f k x =
    trans (zeros-heap ((tsize A ℕ.⊔ tsize B) ℕ.∸ tsize B) f (suc (tsize B) ℕ.+ k) (writeTyped B b (AtStack f (suc k)) (writeLoc x (AtStack f k) (SV-Tag 1))))
          (write-heap B b f (suc k) (writeLoc x (AtStack f k) (SV-Tag 1)))
  write-heap Void v f k x = refl
  write-heap (_ ⇒[ _ ] _) v f k x = refl
  write-heap (μ _) v f k x = refl
  write-heap (ν _ _) v f k x = refl

  store-heap : ∀ {A B} (si : SigOpInfo A B) (x : LocState FS) fr → ans-ok fr (ans-words B) (readReg (LocState.regs x) Output) ≡ true
             → LocState.heapMem (sigop-store si x) ≡ LocState.heapMem x
  store-heap {B = B} si x fr ok = by (in-memory? B) refl (sv-as-loc (readReg (LocState.regs x) Output)) refl (sigop-answer si x)
    where
      o = readReg (LocState.regs x) Output
      by : ∀ im → in-memory? B ≡ im → ∀ ml → sv-as-loc o ≡ ml → ∀ ma
         → LocState.heapMem (sigop-store-at {B = B} im ml ma x) ≡ LocState.heapMem x
      by false _ ml _ ma = refl
      by true _ nothing _ ma = refl
      by true _ (just (AtStack f j)) _ (just v) = write-heap B v f j x
      by true _ (just (AtStack f j)) _ nothing = refl
      by true im (just (AtDynamic hl)) e (just v) = cong LocState.heapMem (Words.write-none (λ r → r) (λ _ → ⊥) (λ _ _ ()) B v (AtDynamic hl) x zero-words)
        where
          ptr : o ≡ SV-Ptr (AtDynamic hl)
          ptr = ptr-of o e
            where
              ptr-of : ∀ v′ → sv-as-loc v′ ≡ just (AtDynamic hl) → v′ ≡ SV-Ptr (AtDynamic hl)
              ptr-of (SV-Ptr _) refl = refl
              ptr-of (SV-Tag _) ()
              ptr-of (SV-Lit _ _) ()
              ptr-of (SV-Code _) ()
          zero-words : tsize B ≡ 0
          zero-words = trans (sym (cong (λ b′ → Data.Bool.if b′ then tsize B else 0) im))
                             (ans-heap fr (ans-words B) hl (subst (λ v′ → ans-ok fr (ans-words B) v′ ≡ true) ptr ok))
      by true _ (just (AtDynamic hl)) _ nothing = refl
