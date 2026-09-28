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
open import DirectedHoTT.Lib.Sugar using ( Cons; []; _∷_; tag; Lt; lt-z; lt-s; []ᵈ; _∷ᵈ_ )
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
open import DirectedHoTT.Examples.Knot.Lookup using ( toTy; hereTy; I∋; ⊢I∋; I∋-sub; ix∋; ⊢ix∋; D∋; ⊢D∋ )
open import DirectedHoTT.Examples.Knot.LookupCon using ( D∋-sub )
open import DirectedHoTT.Lib.FinFam using ( FinI; FinD )
open import DirectedHoTT.Metatheory.RedCong using ( red→≅ᵀ; ⟶ᵀ*-El; ⟶*-⌜IMu⌝ⁱ )
open import DirectedHoTT.Examples.Knot.Sub using ( sub0; ⊢sub0; sub0-sub )
open import DirectedHoTT.Metatheory.TySub using ( ⊢wk )
open import DirectedHoTT.Metatheory.SubjectReductionBase using () renaming ( wk-sub to wkS )

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
⊢CLam {Ξ} {j} {p} {c} dj dp dc =
  PLam.⊢CASE {Ξ} {j} {snd c} {pair (fst c) p} okLamI lt-z dj (⊢tyOf dc) (⊢cI sh-klam ok-klam dj (⊢ctxOf dc) dp)

okLam : RowOK 1 sh-klam rLam
okLam {Ξ} {j} {p} {c} dj dp dc = ⊢rows {Ξ} {JT} {1} {CLam j p c ∷ []} ⊢JT (⊢CLam {Ξ} {j} {p} {c} dj dp dc ∷ᵈ []ᵈ)

------------------------------------------------------------------------
-- ⊢app : Γ ⊢ t ∷ Π A B → Γ ⊢ u ∷ A → Γ ⊢ app t u ∷ B[u]
--   `A`, `B` are not in the subject: σ-fields; `B[u]` is COMPUTED: Ford
--   (`sub0` is opaque — see Knot/Sub)
------------------------------------------------------------------------

w1 w2 : RTm Δ → RTm _
w1 x = renTm vs x
w2 x = renTm vs (renTm vs x)

w2-sub : (σ : Sub Δ Θ) (x : RTm Δ) → subTm (extS (extS σ)) (w2 x) ≡ w2 (subTm σ x)
w2-sub σ x = trans (wkS (extS σ) (w1 x)) (cong w1 (wkS σ x))

TAppI : RTm Δ → RTm Δ → RTm Δ → RTm Δ → RTm Δ → RTm Δ → RTm Δ → Tel Δ
TAppI J G T Q A B X = tρ (tmIx J G T (kPi A B)) (tρ (tmIx J G Q A) (tσ (⌜Id⌝ (⌜Ty⌝ J) X (sub0 0 J B Q)) tι))

TAppI-sub : (σ : Sub Δ Θ) (J G T Q A B X : RTm Δ) →
            subTm σ ⌜ TAppI J G T Q A B X ⌝ᵗ
            ≡ ⌜ TAppI (subTm σ J) (subTm σ G) (subTm σ T) (subTm σ Q) (subTm σ A) (subTm σ B) (subTm σ X) ⌝ᵗ
TAppI-sub σ J G T Q A B X =
  cong₂ (λ Y Z → dρ (tmIx J' (subTm σ G) (subTm σ T) (kPi A' B'))
                   (dρ (tmIx J' (subTm σ G) Q' A') (dσ (⌜Id⌝ Y (subTm σ X) Z) (lam dι))))
        {x = subTm σ (⌜Ty⌝ J)} {x' = ⌜Ty⌝ J'} {y = subTm σ (sub0 0 J B Q)} {y' = sub0 0 J' B' Q'}
        (⌜Ty⌝-sub σ J) (sub0-sub σ 0 J B Q)
  where J' = subTm σ J ; Q' = subTm σ Q ; A' = subTm σ A ; B' = subTm σ B

TAppI-cong : (J J' G G' T T' Q Q' A A' B B' X X' : RTm Δ) → J ≡ J' → G ≡ G' → T ≡ T' → Q ≡ Q' → A ≡ A' → B ≡ B' → X ≡ X' →
             ⌜ TAppI J G T Q A B X ⌝ᵗ ≡ ⌜ TAppI J' G' T' Q' A' B' X' ⌝ᵗ
TAppI-cong J J' G G' T T' Q Q' A A' B B' X X' refl refl refl refl refl refl refl = refl

-- ★ the premises typed at ANY context and positions (instances: the row, the constructor)
okTAppI : {Ξ : Ctx} {J G T Q A B X : RTm ⌊ Ξ ⌋} → Ξ ⊢ J ∷ El ⌜Nat⌝ → Ξ ⊢ G ∷ KCtx J →
          Ξ ⊢ T ∷ K 1 J → Ξ ⊢ Q ∷ K 1 J → Ξ ⊢ A ∷ K 0 J → Ξ ⊢ B ∷ K 0 (nsuc J) → Ξ ⊢ X ∷ K 0 J →
          TelOK Ξ JT (TAppI J G T Q A B X)
okTAppI dJ dG dT dQ dA dB dX =
  ok-ρ (⊢tmIx dJ dG dT (⊢kPi dJ dA dB))
    (ok-ρ (⊢tmIx dJ dG dQ dA)
      (ok-σ (⊢⌜Id⌝ (⊢⌜Ty⌝ dJ) (toTy dX) (toTy (⊢sub0 lt-z dJ dB dQ))) ok-ι))

dσ²-cong : (X X' : RTm Δ) (Y Y' : RTm (Δ ∙)) (Z Z' : RTm ((Δ ∙) ∙)) → X ≡ X' → Y ≡ Y' → Z ≡ Z' →
           dσ X (lam (dσ Y (lam Z))) ≡ dσ X' (lam (dσ Y' (lam Z')))
dσ²-cong X X' Y Y' Z Z' refl refl refl = refl

TApp : RTm Δ → RTm Δ → RTm Δ → Tel Δ
TApp j p c = tσ (⌜Ty⌝ j) (tσ (⌜Ty⌝ (nsuc (w1 j)))
               (TAppI (w2 j) (w2 (fst c)) (w2 (fst p)) (w2 (fst (snd p))) (var (vs vz)) (var vz) (w2 (snd c))))

TApp-law : TelLaw TApp
TApp-law σ j p c =
  dσ²-cong (subTm σ (⌜Ty⌝ j)) (⌜Ty⌝ (subTm σ j))
           (subTm (extS σ) (⌜Ty⌝ (nsuc (w1 j)))) (⌜Ty⌝ (nsuc (w1 (subTm σ j))))
           (subTm (extS (extS σ)) ⌜ TAppI (w2 j) (w2 (fst c)) (w2 (fst p)) (w2 (fst (snd p))) (var (vs vz)) (var vz) (w2 (snd c)) ⌝ᵗ)
           ⌜ TAppI (w2 (subTm σ j)) (w2 (fst (subTm σ c))) (w2 (fst (subTm σ p))) (w2 (fst (snd (subTm σ p)))) (var (vs vz)) (var vz) (w2 (snd (subTm σ c))) ⌝ᵗ
           (⌜Ty⌝-sub σ j)
           (trans (⌜Ty⌝-sub (extS σ) (nsuc (w1 j))) (cong (λ z → ⌜Ty⌝ (nsuc z)) {x = subTm (extS σ) (w1 j)} {y = w1 (subTm σ j)} (wkS σ j)))
           (trans (TAppI-sub (extS (extS σ)) (w2 j) (w2 (fst c)) (w2 (fst p)) (w2 (fst (snd p))) (var (vs vz)) (var vz) (w2 (snd c)))
                  (TAppI-cong _ _ _ _ _ _ _ _ _ _ _ _ _ _ (w2-sub σ j) (w2-sub σ (fst c)) (w2-sub σ (fst p)) (w2-sub σ (fst (snd p))) refl refl (w2-sub σ (snd c))))

rApp : Row
rApp = defRow TApp TApp-law

okAppT : {Ξ : Ctx} {j p c : RTm ⌊ Ξ ⌋} → Ξ ⊢ j ∷ El ⌜Nat⌝ →
         Ξ ⊢ p ∷ PayV sh-kapp (pair (tag 1) j) (SI 2) (SD KSig) → Ξ ⊢ c ∷ El (CTat (pair (tag 1) j)) →
         TelOK Ξ JT (TApp j p c)
okAppT {Ξ} {j} {p} {c} dj dp dc =
  ok-σ (⊢⌜Ty⌝ dj) (subst (λ X → TelOK Ξ₁ X T₁) (sym (JT-ren vs))
    (ok-σ (⊢⌜Ty⌝ (⊢isuc dj₁)) (subst (λ X → TelOK Ξ₂ X T₂) (sym (JT-ren vs)) okI)))
  where
    Ξ₁ Ξ₂ : Ctx
    Ξ₁ = Ξ ▹ El (⌜Ty⌝ j)
    Ξ₂ = Ξ₁ ▹ El (⌜Ty⌝ (nsuc (w1 j)))
    T₂ = TAppI (w2 j) (w2 (fst c)) (w2 (fst p)) (w2 (fst (snd p))) (var (vs vz)) (var vz) (w2 (snd c))
    T₁ = tσ (⌜Ty⌝ (nsuc (w1 j))) T₂
    dj₁ : Ξ₁ ⊢ w1 j ∷ El ⌜Nat⌝
    dj₁ = ⊢wk {Ξ} {El (⌜Ty⌝ j)} {j} {El ⌜Nat⌝} dj
    dj₂ : Ξ₂ ⊢ w2 j ∷ El ⌜Nat⌝
    dj₂ = ⊢wk {Ξ₁} {El (⌜Ty⌝ (nsuc (w1 j)))} {w1 j} {El ⌜Nat⌝} dj₁
    wk2K : {s : ℕ} {d x : RTm ⌊ Ξ ⌋} → Ξ ⊢ x ∷ K s d → Ξ₂ ⊢ w2 x ∷ K s (w2 d)
    wk2K {s} {d} {x} dx = ⊢wkSK {Γ = Ξ₁} {B = El (⌜Ty⌝ (nsuc (w1 j)))} {sg = KSig} {s = s} {d = w1 d} {t = w1 x}
                            (⊢wkSK {Γ = Ξ} {B = El (⌜Ty⌝ j)} {sg = KSig} {s = s} {d = d} {t = x} dx)
    dg₂ : Ξ₂ ⊢ w2 (fst c) ∷ KCtx (w2 j)
    dg₂ = ⊢wkCtx {Ξ₁} {El (⌜Ty⌝ (nsuc (w1 j)))} {w1 j} {w1 (fst c)} (⊢wkCtx {Ξ} {El (⌜Ty⌝ j)} {j} {fst c} (⊢ctxOf dc))
    dt = wk2K (g0 1 0 (rec 1 0 ∷ʰ []ʰ) dp)
    du = wk2K (g0 1 0 []ʰ (⊢recSnd {s = 1} {k = 0} {sh = rec 1 0 ∷ʰ []ʰ} dp))
    dA : Ξ₂ ⊢ var (vs vz) ∷ K 0 (w2 j)
    dA = ⊢wkSK {Γ = Ξ₁} {B = El (⌜Ty⌝ (nsuc (w1 j)))} {sg = KSig} {s = 0} {d = w1 j} {t = var vz} (hereTy {Ξ} {j})
    dB : Ξ₂ ⊢ var vz ∷ K 0 (nsuc (w2 j))
    dB = hereTy {Ξ₁} {nsuc (w1 j)}
    okI : TelOK Ξ₂ JT T₂
    okI = okTAppI dj₂ dg₂ dt du dA dB (wk2K (⊢tyOf dc))

okApp : RowOK 1 sh-kapp rApp
okApp {Ξ} {j} {p} {c} dj dp dc = ⊢rows {Ξ} {JT} {1} {⌜ TApp j p c ⌝ᵗ ∷ []} ⊢JT (⊢tel {Ξ} {JT} {TApp j p c} ⊢JT (okAppT dj dp dc) ∷ᵈ []ᵈ)

------------------------------------------------------------------------
-- ⊢var : Γ ∋ x ∷ A → Γ ⊢ var x ∷ A
--   the premise is of a LOWER stratum (∋): a σ-field of its code (D077)
------------------------------------------------------------------------

TVar : RTm Δ → RTm Δ → RTm Δ → Tel Δ
TVar j p c = tσ (⌜IMu⌝ I∋ D∋ (ix∋ j (fst c) (fst p) (snd c))) tι

imu-cong : (I I' D D' i : RTm Δ) → I ≡ I' → D ≡ D' → dσ (⌜IMu⌝ I D i) (lam dι) ≡ dσ (⌜IMu⌝ I' D' i) (lam dι)
imu-cong I I' D D' i refl refl = refl

TVar-law : TelLaw TVar
TVar-law σ j p c = imu-cong _ _ _ _ _ (I∋-sub σ) (D∋-sub σ)

rVar : Row
rVar = defRow TVar TVar-law

-- a variable payload's field, at the depth
⊢varOf : {Ξ : Ctx} {j p : RTm ⌊ Ξ ⌋} → Ξ ⊢ p ∷ PayV sh-kvar (pair (tag 1) j) (SI 2) (SD KSig) → Ξ ⊢ fst p ∷ FinI j
⊢varOf {j = j} dp = ⊢conv (⊢fst dp) (ctrnᵀ (red→≅ᵀ (⟶ᵀ*-El (⟶*-⌜IMu⌝ⁱ (step (βsnd (tag 1) j) done)))) (credᵀ El-⌜IMu⌝))

okVarT : {Ξ : Ctx} {j p c : RTm ⌊ Ξ ⌋} → Ξ ⊢ j ∷ El ⌜Nat⌝ →
         Ξ ⊢ p ∷ PayV sh-kvar (pair (tag 1) j) (SI 2) (SD KSig) → Ξ ⊢ c ∷ El (CTat (pair (tag 1) j)) →
         TelOK Ξ JT (TVar j p c)
okVarT dj dp dc = ok-σ (⊢⌜IMu⌝ ⊢I∋ ⊢D∋ (⊢ix∋ dj (⊢ctxOf dc) (⊢varOf dp) (⊢tyOf dc))) ok-ι

okVar : RowOK 1 sh-kvar rVar
okVar {Ξ} {j} {p} {c} dj dp dc = ⊢rows {Ξ} {JT} {1} {⌜ TVar j p c ⌝ᵗ ∷ []} ⊢JT (⊢tel {Ξ} {JT} {TVar j p c} ⊢JT (okVarT dj dp dc) ∷ᵈ []ᵈ)
