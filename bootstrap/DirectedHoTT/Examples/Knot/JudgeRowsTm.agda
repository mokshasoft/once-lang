------------------------------------------------------------------------
-- OCP-0009 · KNOT — the `⊢` ROWS of the typing judgement (D077).
--
-- A rule whose conclusion TYPE is a constructor pattern is a NESTED CASE
-- on the convoy's type (`Lib/SynPat`): the pattern's variables are the
-- type's payload, the case's convoy is `(Γ , term payload)`
-- (`JudgeTmIx`).  A computed conclusion type Fords (`⌜Id⌝` field).
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.JudgeRowsTm where

open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong; cong₂; subst )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax hiding ( Fin )
open import DirectedHoTT.Spec.Typing hiding ( _×_; _,,_ )
open import DirectedHoTT.Lib.Sugar using ( Cons; []; _∷_; tag; lt-z; lt-s; []ᵈ; _∷ᵈ_ )
open import DirectedHoTT.Lib.SynView using ( PayV; ⊢recFst; ⊢recSnd; ⊢atDepth )
open import DirectedHoTT.Lib.FinFam using ( ⊢isuc )
open import DirectedHoTT.Examples.Knot.Ctors
open import DirectedHoTT.Lib.Tel
open import DirectedHoTT.Lib.Syn
open import DirectedHoTT.Lib.SynFib using ( Row )
open import DirectedHoTT.Lib.SynPat using ( module Pat )
open import DirectedHoTT.Examples.Knot.Sig
open import DirectedHoTT.Examples.Knot.Ctx
open import DirectedHoTT.Examples.Knot.Lookup using ( rows; ⊢rows )
open import DirectedHoTT.Examples.Knot.JudgeIx
open import DirectedHoTT.Examples.Knot.JudgeTmIx
open import DirectedHoTT.Examples.Knot.JudgeRowsTy using ( RowOK; f0; r1 )

private
  variable
    Δ Θ : Cx

-- a TERM payload's field (index `(1 , j)`), its depth read off
g0 : {Ξ : Ctx} {j p : RTm ⌊ Ξ ⌋} (s k : ℕ) (sh : Shape) →
     Ξ ⊢ p ∷ PayV (rec s k ∷ʰ sh) (pair (tag 1) j) (SI 2) (SD KSig) → Ξ ⊢ fst p ∷ K s (nsucs k j)
g0 {j = j} s k sh dp = ⊢atDepth {a = tag 1} {j = j} {s = s} {k = k} (⊢recFst {s = s} {k = k} {sh = sh} dp)

------------------------------------------------------------------------
-- ⊢lam : Γ ⊢ty A → (Γ ▹ A) ⊢ t ∷ B → Γ ⊢ lam t ∷ Π A B
--   case on the type at `Π`; `q = (A , B)`, the convoy `(Γ , (t))`
------------------------------------------------------------------------

TLam : RTm Δ → RTm Δ → RTm Δ → Tel Δ
TLam j q c = tρ (tyIx j (fst c) (fst q)) (tρ (tmIx (nsuc j) (cext (fst c) (fst q)) (fst (snd c)) (fst (snd q))) tι)

rLamI : Row
rLamI = record { R = λ j q c → ⌜ TLam j q c ⌝ᵗ ; R-sub = λ σ j q c → refl }

module PLam = Pat KOK JT JT-sub ⊢JT (CI sh-klam) (CI-sub sh-klam) (⊢CI ok-klam) 0 2 rLamI

okLamT : {Ξ : Ctx} {j q c : RTm ⌊ Ξ ⌋} → Ξ ⊢ j ∷ El ⌜Nat⌝ →
         Ξ ⊢ q ∷ PayV sh-kPi (pair (tag 0) j) (SI 2) (SD KSig) → Ξ ⊢ c ∷ El (CIat sh-klam (pair (tag 0) j)) →
         TelOK Ξ JT (TLam j q c)
okLamT dj dq dc = ok-ρ (⊢tyIx dj dg dA) (ok-ρ (⊢tmIx (⊢isuc dj) (⊢cext dj dg dA) dt dB) ok-ι)
  where dg = ⊢gI sh-klam dc
        dA = f0 0 0 (rec 0 1 ∷ʰ []ʰ) dq
        dB = f0 0 1 []ʰ (r1 0 0 (rec 0 1 ∷ʰ []ʰ) dq)
        dt = g0 1 1 []ʰ (⊢pI sh-klam dc)

okLamI : PLam.RowOK 0 sh-kPi rLamI
okLamI {Ξ} {j} {q} {c} dj dq dc = ⊢tel {Ξ} {JT} {TLam j q c} ⊢JT (okLamT dj dq dc)

-- the outer row: one rule, the case on the type
CLam : RTm Δ → RTm Δ → RTm Δ → RTm Δ
CLam j p c = PLam.CASE j (snd c) (pair (fst c) p)

rLam : Row
rLam = record
  { R = λ j p c → rows (CLam j p c ∷ [])
  ; R-sub = λ σ j p c →
      trans (rows-sub' σ (CLam j p c ∷ []))
            (cong (λ X → rows (X ∷ [])) {x = subTm σ (CLam j p c)} {y = CLam (subTm σ j) (subTm σ p) (subTm σ c)}
                  (PLam.CASE-sub σ j (snd c) (pair (fst c) p))) }

⊢CLam : {Ξ : Ctx} {j p c : RTm ⌊ Ξ ⌋} → Ξ ⊢ j ∷ El ⌜Nat⌝ →
        Ξ ⊢ p ∷ PayV sh-klam (pair (tag 1) j) (SI 2) (SD KSig) → Ξ ⊢ c ∷ El (CTat (pair (tag 1) j)) →
        Ξ ⊢ CLam j p c ∷ Desc JT
⊢CLam dj dp dc = PLam.⊢CASE okLamI lt-z dj (⊢tyOf dc) (⊢cI sh-klam ok-klam dj (⊢ctxOf dc) dp)

okLam : RowOK 1 sh-klam rLam
okLam dj dp dc = ⊢rows ⊢JT (⊢CLam dj dp dc ∷ᵈ []ᵈ)
