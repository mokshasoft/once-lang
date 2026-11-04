-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.CallsLinked   (plan 0.103 6a‴, D245; plan 0.129 B5)
--
-- EVERY EMITTED CALL IS ONE ITS LEAF VOUCHES FOR: each `c-call-fn f` in the
-- trace of an IR whose calls satisfy `C i` satisfies `C i` at some objects, and
-- each `instr-sigop si` satisfies `Q` when every SigOp leaf's lowering does
-- (`Calls`). The emitter writes `c-call-fn f` for `Call f` and `instr-sigop`
-- for a SigOp (a comparison: its block, `cmp-trace`) and nowhere else, so the
-- induction is `AllocMin`'s (`All P` over the entry block and the block
-- channel), with the leaf facts threaded to the leaves. plan 0.123 B.4 α: the
-- flat layout's code calls nothing (`FlatLayout`'s `All` lemmas).
------------------------------------------------------------------------

open import Once.Spec.Name using (CanonicalName)
open import Once.IRTy using (IRTy)
open import Once.SigOp.Info using (SigOpInfo)

module Once.CCC.Codegen.CallsLinked (o : CanonicalName) {I : Set}
  (C : I → CanonicalName → IRTy → IRTy → Set) (i : I) (Q : ∀ {A B} → SigOpInfo A B → Set) where

open import Data.Nat using (ℕ; suc; _+_; _*_; _⊔_; _∸_)
open import Data.Unit using (tt)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.All.Properties using (++⁺)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import Once.IR using (IR; id; _∘_; ⟨_,_⟩; fst; snd; inl; inr; case; terminal; initial; curry; apply; In; out-μ; Cata; Out; in-ν; Ana; Iter; SigOp; Call; const)
open import Once.IRTy using (IRFunctor; ⟦_⟧TI; ν-type; fits-int; fits-float; ⌈_⌉F; WellFormedFI; wf-K; wf-Id; wf-Sum; wf-Prod) renaming (_+_ to _+ᵀ_)
open import Once.Spec.Type using (Fun; K; Id; _⊕_; _⊗_)
open import Once.CCC.Label using (ℓ)
open import Once.CCC.Machine.MuRep using (MuRep; mu-box; mu-unit; mu-ptr; mu-rep)
open import Once.CCC.Machine.SMCore using (AbstractInstr; AbstractTrace; blocks-layout; blocks-layout-++; LabelId; link-top)
import Once.CCC.Machine.SMCore as SM
open import Once.SigOp.Info using (module SigOpInfo)
open SigOpInfo using (sem)
open import Once.Denotation.Program using (Leaves)
open import Once.Arith.CmpOp using (CmpOp)
open import Once.Arith.SigOp.Compare using (cmp-of)
open import Once.CCC.Codegen.FlatLayout
  using (Kind; word; flat; kind; put; put-k; get; get-k; fill; put-All; put-k-All; get-All; get-k-All; fill-All; lkind; lsz)
open import Once.CCC.Codegen.IRToTrace o using
  (sigop-code; ir-to-trace'; ir-to-trace; ir-to-trace-lab; ir-to-unit; strat-const; strat-box; strat-branching; cata-strategy; cata-dispatch; cata-trace-branching; cata-trace-box; cata-call-box; in-trace; out-trace; push2; pop2; wrap-sum; visit-walk; rebuild-walk; lsize; cata-body; cata-call-setup; cata-call; cata-call-from; cata-trace-const; fsize; resuspend-layer; env-entry; env-prologue; inj-trace)
open import Once.CCC.Codegen.FrameFreeTrace o using (trace-of; cata-trace-of)
import Once.CCC.Codegen.Size

open import Once.CCC.Codegen.CallOK using (InstrOK; Calls)

P : AbstractInstr → Set
P = InstrOK (C i) Q

CLTrace : AbstractTrace → Set
CLTrace = All P

LK : ∀ {A B} → IR A B → Set
LK = Leaves C i (λ si → Calls Q si (cmp-of (sem si)))

------------------------------------------------------------------------
-- plan 0.123 B.4 α: the layout code calls nothing.
------------------------------------------------------------------------
put-cl : ∀ X s b o′ → CLTrace (put X s b o′)
put-cl X s b o′ = put-All {P} X s b o′ tt tt tt (λ _ → tt) (λ _ → tt)

put-k-cl : ∀ kd n s b o′ → CLTrace (put-k kd n s b o′)
put-k-cl kd n s b o′ = put-k-All {P} kd n s b o′ tt tt tt (λ _ → tt) (λ _ → tt)

get-cl : ∀ X k → CLTrace (get X k)
get-cl X k = get-All {P} X k (λ _ → tt) (λ _ → tt) tt

get-k-cl : ∀ kd n k → CLTrace (get-k kd n k)
get-k-cl kd n k = get-k-All {P} kd n k (λ _ → tt) (λ _ → tt) tt

fill-cl : ∀ from c → CLTrace (fill from c)
fill-cl from c = fill-All {P} from c tt (λ _ → tt)

inj-cl : ∀ t P′ S n → CLTrace (inj-trace t P′ S n)
inj-cl t P′ S n = tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ ++⁺ (fill-cl _ (Once.CCC.Codegen.Size.size S ∸ suc (Once.CCC.Codegen.Size.size P′))) (++⁺ (put-cl P′ n (suc n) 1) (tt ∷ []))

env-entry-cl : ∀ kd E A → CLTrace (proj₂ (env-entry kd E A))
env-entry-cl word E A = []
env-entry-cl flat E A =
  tt ∷ tt ∷ tt ∷ tt ∷ tt ∷
  ++⁺ (get-cl A 1)
      (tt ∷ tt ∷ tt ∷
       ++⁺ (put-cl E 1 3 0) (++⁺ (put-cl A 2 3 _) (tt ∷ tt ∷ [])))

push2-cl : ∀ topSlot tv tb → CLTrace (push2 topSlot tv tb)
push2-cl topSlot tv tb = tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ []

pop2-cl : ∀ topSlot → CLTrace (pop2 topSlot)
pop2-cl topSlot = tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ []

wrap-sum-cl : ∀ tag pk ps ss s → CLTrace (wrap-sum tag pk ps ss s)
wrap-sum-cl tag pk ps ss s =
  tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ ++⁺ (fill-cl _ (ss ∸ suc ps)) (++⁺ (put-k-cl pk ps s (suc s) 1) (tt ∷ []))

getμ-cl : ∀ (G : Fun 0) k → CLTrace (get-k (lkind G word) (lsz G 1) k)
getμ-cl G k = get-k-cl (lkind G word) (lsz G 1) k

visit-walk-cl : ∀ todoSlot tv tb F s lb → CLTrace (visit-walk todoSlot tv tb F s lb)
visit-walk-cl todoSlot tv tb (K _)   s lb = []
visit-walk-cl todoSlot tv tb Id      s lb = tt ∷ push2-cl todoSlot tv tb
visit-walk-cl todoSlot tv tb (F ⊕ G) s lb =
  ++⁺ (tt ∷ []) (++⁺ (getμ-cl G 1) (++⁺ (tt ∷ [])
  (++⁺ (visit-walk-cl todoSlot tv tb G (s + 4) (suc (suc lb) + lsize F)) (++⁺ (tt ∷ tt ∷ [])
  (++⁺ (getμ-cl F 1) (++⁺ (tt ∷ [])
  (++⁺ (visit-walk-cl todoSlot tv tb F (s + 4) (suc (suc lb))) (tt ∷ []))))))))
visit-walk-cl todoSlot tv tb (F ⊗ G) s lb =
  ++⁺ (tt ∷ tt ∷ []) (++⁺ (getμ-cl F 0) (++⁺ (tt ∷ [])
  (++⁺ (visit-walk-cl todoSlot tv tb F (s + 4) lb) (++⁺ (tt ∷ [])
  (++⁺ (getμ-cl G (lsz F 1)) (++⁺ (tt ∷ [])
       (visit-walk-cl todoSlot tv tb G (s + 4) (lb + lsize F))))))))

rebuild-walk-cl : ∀ valSlot tv tb ck cs F s lb → CLTrace (rebuild-walk valSlot tv tb ck cs F s lb)
rebuild-walk-cl valSlot tv tb ck cs (K _)   s lb = tt ∷ []
rebuild-walk-cl valSlot tv tb ck cs Id      s lb = pop2-cl valSlot
rebuild-walk-cl valSlot tv tb ck cs (F ⊕ G) s lb =
  ++⁺ (tt ∷ []) (++⁺ (getμ-cl G 1) (++⁺ (tt ∷ [])
  (++⁺ (rebuild-walk-cl valSlot tv tb ck cs G (s + 4) (suc (suc lb) + lsize F))
  (++⁺ (wrap-sum-cl 1 (lkind G ck) (lsz G cs) (lsz (F ⊕ G) cs) s) (++⁺ (tt ∷ tt ∷ [])
  (++⁺ (getμ-cl F 1) (++⁺ (tt ∷ [])
  (++⁺ (rebuild-walk-cl valSlot tv tb ck cs F (s + 4) (suc (suc lb)))
  (++⁺ (wrap-sum-cl 0 (lkind F ck) (lsz F cs) (lsz (F ⊕ G) cs) s) (tt ∷ []))))))))))
rebuild-walk-cl valSlot tv tb ck cs (F ⊗ G) s lb =
  ++⁺ (tt ∷ tt ∷ []) (++⁺ (getμ-cl G (lsz F 1)) (++⁺ (tt ∷ [])
  (++⁺ (rebuild-walk-cl valSlot tv tb ck cs G (s + 4) (lb + lsize F)) (++⁺ (tt ∷ tt ∷ [])
  (++⁺ (getμ-cl F 0) (++⁺ (tt ∷ [])
  (++⁺ (rebuild-walk-cl valSlot tv tb ck cs F (s + 4) lb) (++⁺ (tt ∷ tt ∷ tt ∷ [])
  (++⁺ (put-k-cl (lkind F ck) (lsz F cs) (suc s) (s + 3) 0)
  (++⁺ (put-k-cl (lkind G ck) (lsz G cs) (s + 2) (s + 3) (lsz F cs)) (tt ∷ [])))))))))))

cata-body-cl : ∀ b e bb at → CLTrace at → CLTrace (cata-body b e bb at)
cata-body-cl b e bb at ih = tt ∷ tt ∷ ++⁺ ih (tt ∷ tt ∷ [])

cata-setup-cl : ∀ E cl k ev bl → CLTrace (cata-call-setup E cl k ev bl)
cata-setup-cl E cl k ev bl =
  ++⁺ (get-cl E 0) (tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ [])

cata-call-from-cl : ∀ i0 → P i0 → ∀ E lk ls cl k ev pr → CLTrace (cata-call-from i0 E lk ls cl k ev pr)
cata-call-from-cl i0 p0 E lk ls cl k ev pr =
  p0 ∷ tt ∷ tt ∷ tt ∷
  ++⁺ (put-cl E ev pr 0) (++⁺ (put-k-cl lk ls k pr _) (tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ []))

cata-const-cl : ∀ E G bb n1 l1 at → CLTrace at
              → CLTrace (cata-trace-of (cata-trace-const E G bb n1 l1 at))
cata-const-cl E G bb n1 l1 at ih =
  ++⁺ (cata-setup-cl E n1 (n1 + 1) (n1 + 2) l1)
      (++⁺ (cata-call-from-cl _ tt E (lkind G word) (lsz G 1) n1 (n1 + 1) (n1 + 2) (n1 + 3)) (cata-body-cl l1 (l1 + 1) bb at ih))

cata-box-cl : ∀ E G bb n1 l1 at → CLTrace at
              → CLTrace (cata-trace-of (cata-trace-box E G bb n1 l1 at))
cata-box-cl E G bb n1 l1 at ih =
  ++⁺ (cata-setup-cl E n1 (n1 + 1) (n1 + 2) l1)
      (++⁺ (cata-call-from-cl _ tt E (lkind G word) (lsz G 1) n1 (n1 + 1) (n1 + 2) (n1 + 3)) (cata-body-cl l1 (l1 + 1) bb at ih))

cata-branching-cl : ∀ E A F bb n1 l1 at → CLTrace at
                  → CLTrace (cata-trace-of (cata-trace-branching E A F bb n1 l1 at))
cata-branching-cl E A F bb n1 l1 at ih =
  ++⁺ (cata-setup-cl E cl (cl + 1) (cl + 2) bodyL)
      (++⁺ I₁ (++⁺ (cata-call-from-cl _ tt E (lkind F (kind A)) (lsz F (Once.CCC.Codegen.Size.size A)) cl (cl + 1) (cl + 2) (cl + 3))
                   (++⁺ I₂ (cata-body-cl bodyL (bodyL + 1) bb at ih))))
  where
    bodyL = l1 + 4 + lsize F + lsize F
    cl    = n1 + 7 + (4 * fsize F) + 4
    I₁ : CLTrace _
    I₁ = ++⁺ (tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ [])
             (++⁺ (push2-cl n1 (n1 + 4) (n1 + 5))
             (++⁺ (tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ [])
             (++⁺ (push2-cl (suc n1) (n1 + 4) (n1 + 5))
             (++⁺ (tt ∷ tt ∷ [])
             (++⁺ (visit-walk-cl n1 (n1 + 4) (n1 + 5) F (n1 + 7) (l1 + 4))
             (++⁺ (tt ∷ tt ∷ [])
             (++⁺ (tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ [])
             (++⁺ (rebuild-walk-cl (n1 + 2) (n1 + 4) (n1 + 5) (kind A) _ F (n1 + 7) ((l1 + 4) + lsize F))
                  (tt ∷ [])))))))))
    I₂ : CLTrace _
    I₂ = ++⁺ (push2-cl (n1 + 2) (n1 + 4) (n1 + 5))
             (++⁺ (tt ∷ tt ∷ []) (tt ∷ tt ∷ tt ∷ []))

cata-dispatch-cl : ∀ E A G st bb n1 l1 at → CLTrace at
                 → CLTrace (cata-trace-of (cata-dispatch E A G st bb n1 l1 at))
cata-dispatch-cl E A G strat-const         bb n1 l1 at ih = cata-const-cl E G bb n1 l1 at ih
cata-dispatch-cl E A G strat-box           bb n1 l1 at ih = cata-box-cl E G bb n1 l1 at ih
cata-dispatch-cl E A G (strat-branching F) bb n1 l1 at ih = cata-branching-cl E A F bb n1 l1 at ih


sigop-calls : ∀ {A B} (si : SigOpInfo A B) (n : ℕ) (m : Maybe CmpOp) → Calls Q si m → CLTrace (sigop-code si n m)
sigop-calls si n nothing  q = q ∷ []
sigop-calls si n (just _) q = q ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ []

in-cl : ∀ (r : MuRep) (n : ℕ) → CLTrace (in-trace r n)
in-cl mu-box  n = tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ []
in-cl mu-unit n = tt ∷ []
in-cl mu-ptr  n = tt ∷ []

out-cl : ∀ (r : MuRep) → CLTrace (out-trace r)
out-cl mu-box  = tt ∷ []
out-cl mu-unit = tt ∷ []
out-cl mu-ptr  = tt ∷ []

calls-trace' : ∀ {A B} (ir : IR A B) (n l : ℕ) → LK ir
             → CLTrace (trace-of (ir-to-trace' n l ir))
calls-trace' id       n l _ = tt ∷ []
calls-trace' (fst {A} {B}) n l _ = get-cl A 0
calls-trace' (snd {A} {B}) n l _ = get-cl B _
calls-trace' terminal n l _ = []
calls-trace' initial  n l _ = tt ∷ []
calls-trace' (g ∘ f)  n l (lg , lf) =
  ++⁺ (calls-trace' f _ _ lf) (tt ∷ calls-trace' g _ _ lg)
calls-trace' (⟨_,_⟩ {A} {B} {C′} f g) n l (lf , lg) =
  tt ∷ tt ∷
  ++⁺ (calls-trace' f _ _ lf)
      (tt ∷ tt ∷
       ++⁺ (calls-trace' g _ _ lg)
           (tt ∷ tt ∷ tt ∷ ++⁺ (put-cl B _ _ 0) (++⁺ (put-cl C′ _ _ _) (tt ∷ []))))
calls-trace' (curry b)  n l _ =
  tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ []
calls-trace' (apply {A} {B}) n l _ =
  ++⁺ (get-cl A 1)
      (tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷
       ++⁺ (put-cl A _ _ 1) (tt ∷ tt ∷ tt ∷ []))
calls-trace' (inl {A} {B}) n l _ = inj-cl 0 A (A +ᵀ B) n
calls-trace' (inr {A} {B}) n l _ = inj-cl 1 B (A +ᵀ B) n
calls-trace' (case {A} {B} f g) n l (lf , lg) =
  ++⁺ (tt ∷ []) (++⁺ (get-cl B 1) (++⁺ (tt ∷ [])
  (++⁺ (calls-trace' g _ _ lg) (++⁺ (tt ∷ tt ∷ [])
  (++⁺ (get-cl A 1) (++⁺ (tt ∷ [])
  (++⁺ (calls-trace' f _ _ lf) (tt ∷ []))))))))
calls-trace' (In {F} _) n l _ = in-cl (mu-rep F) n
calls-trace' (out-μ {F} _) n l _ = out-cl (mu-rep F)
calls-trace' (Cata {F} _ {E} {A} alg) n l la =
  cata-dispatch-cl E A ⌈ F ⌉F (cata-strategy ⌈ F ⌉F) _ _ _ _ (calls-trace' alg 0 l la)
calls-trace' (Out _)        n l _ = tt ∷ tt ∷ tt ∷ tt ∷ []
calls-trace' (in-ν _)     n l _ =
  tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ []
calls-trace' (Ana _ c)      n l _ =
  tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ []
calls-trace' (Iter {E} {A} {B} b) n l lb =
  ++⁺ (get-cl E 0) (++⁺ (tt ∷ tt ∷ [])
  (++⁺ (calls-trace' b _ _ lb) (++⁺ (tt ∷ tt ∷ [])
  (++⁺ (get-cl A 1) (++⁺ (tt ∷ tt ∷ tt ∷ [])
  (++⁺ (put-cl E _ _ 0) (++⁺ (put-cl A _ _ _)
  (++⁺ (tt ∷ tt ∷ tt ∷ tt ∷ []) (get-cl B 1)))))))))
calls-trace' (SigOp si)     n l q = sigop-calls si n (cmp-of (sem si)) q
calls-trace' (Call {A} {B} f) n l lk = (A , B , lk) ∷ []
calls-trace' (const fits-int _)   n l _ = tt ∷ []
calls-trace' (const fits-float _) n l _ = tt ∷ []


bodies-of : ℕ × ℕ × AbstractTrace × List (LabelId × ℕ × AbstractTrace)
          → List (LabelId × ℕ × AbstractTrace)
bodies-of (_ , _ , _ , bs) = bs

bud : ℕ × ℕ × AbstractTrace × List (LabelId × ℕ × AbstractTrace) → ℕ
bud (b , _ , _ , _) = b

lab : ℕ × ℕ × AbstractTrace × List (LabelId × ℕ × AbstractTrace) → ℕ
lab (_ , k , _ , _) = k

resuspend-cl : ∀ (H : IRFunctor) (E A : IRTy) (n l : ℕ) (lbl : LabelId) (env : ℕ) {F} (wf : WellFormedFI F)
             → CLTrace (proj₂ (proj₂ (resuspend-layer H E A n l lbl env wf)))
resuspend-cl H E A n l lbl env (wf-K _) = []
resuspend-cl H E A n l lbl env wf-Id =
  ++⁺ (tt ∷ tt ∷ []) (++⁺ (get-cl E 0) (++⁺ (tt ∷ tt ∷ tt ∷ [])
  (++⁺ (put-cl E _ _ 0) (++⁺ (put-cl A _ _ _)
       (tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ [])))))
resuspend-cl H E A n l lbl env (wf-Prod {F} {G} wfF wfG) =
  ++⁺ (tt ∷ tt ∷ []) (++⁺ (get-cl (⟦ F ⟧TI A) 0)
  (++⁺ (resuspend-cl H E A (suc (suc (suc (suc n)))) l lbl env wfF) (++⁺ (tt ∷ tt ∷ [])
  (++⁺ (get-cl (⟦ G ⟧TI A) _) (++⁺ (resuspend-cl H E A n2 l2 lbl env wfG)
  (++⁺ (tt ∷ tt ∷ tt ∷ [])
  (++⁺ (put-cl (⟦ F ⟧TI (ν-type H)) _ _ 0) (++⁺ (put-cl (⟦ G ⟧TI (ν-type H)) _ _ _) (tt ∷ [])))))))))
  where
    n2 = proj₁ (resuspend-layer H E A (suc (suc (suc (suc n)))) l lbl env wfF)
    l2 = proj₁ (proj₂ (resuspend-layer H E A (suc (suc (suc (suc n)))) l lbl env wfF))
resuspend-cl H E A n l lbl env (wf-Sum {F} {G} wfF wfG) =
  ++⁺ (tt ∷ tt ∷ tt ∷ [])
      (++⁺ (arm G (resuspend-cl H E A n2 l2 lbl env wfG) {c = c-of G})
      (++⁺ (tt ∷ tt ∷ [])
      (++⁺ (arm F (resuspend-cl H E A (suc (suc (suc n))) (suc (suc l)) lbl env wfF) {c = c-of F}) (tt ∷ []))))
  where
    Sz = Once.CCC.Codegen.Size.size
    c-of : IRFunctor → ℕ
    c-of P = Sz (⟦ F ⟧TI (ν-type H) +ᵀ ⟦ G ⟧TI (ν-type H)) ∸ suc (Sz (⟦ P ⟧TI (ν-type H)))
    n2 = proj₁ (resuspend-layer H E A (suc (suc (suc n))) (suc (suc l)) lbl env wfF)
    l2 = proj₁ (proj₂ (resuspend-layer H E A (suc (suc (suc n))) (suc (suc l)) lbl env wfF))
    arm : ∀ (P′ : IRFunctor) {t} → CLTrace t → ∀ {tag sz c}
        → CLTrace ((SM.restore-input n ∷ []) ++ get (⟦ P′ ⟧TI A) 1 ++ t ++
                   (SM.store-at-slot (suc (suc n)) ∷ SM.instr-alloc-heap sz ∷
                    SM.store-at-slot (suc n) ∷ SM.mov-to-input ∷
                    SM.instr-load-tag-lit tag ∷ SM.store-at 0 ∷ []) ++
                   fill (suc (Once.CCC.Codegen.Size.size (⟦ P′ ⟧TI (ν-type H)))) c ++
                   put (⟦ P′ ⟧TI (ν-type H)) (suc (suc n)) (suc n) 1 ++
                   (SM.load-from-slot (suc n) ∷ []))
    arm P′ ih {c = c} =
      ++⁺ (tt ∷ []) (++⁺ (get-cl (⟦ P′ ⟧TI A) 1) (++⁺ ih
      (++⁺ (tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ []) (++⁺ (fill-cl _ c) (++⁺ (put-cl (⟦ P′ ⟧TI (ν-type H)) _ _ 1) (tt ∷ []))))))

calls-blocks : ∀ {A B} (ir : IR A B) (n l : ℕ) → LK ir
             → CLTrace (blocks-layout (bodies-of (ir-to-trace' n l ir)))
calls-blocks id       n l _ = []
calls-blocks fst      n l _ = []
calls-blocks snd      n l _ = []
calls-blocks terminal n l _ = []
calls-blocks initial  n l _ = []
calls-blocks apply    n l _ = []
calls-blocks inl n l _ = []
calls-blocks inr n l _ = []
calls-blocks (In _)   n l _ = []
calls-blocks (out-μ _)  n l _ = []
calls-blocks (Out _)    n l _ = []
calls-blocks (in-ν _) n l _ = tt ∷ tt ∷ tt ∷ []
calls-blocks (Ana {F} wf {E} {A} c) n l lc =
  ++⁺ (tt ∷ ++⁺ (tt ∷ tt ∷ (++⁺ (calls-trace' c 1 (suc l) lc)
                     (resuspend-cl F E A (proj₁ (ir-to-trace' 1 (suc l) c))
                                   (proj₁ (proj₂ (ir-to-trace' 1 (suc l) c)))
                                   (ℓ o l) 0 wf)))
                (tt ∷ []))
      (calls-blocks c 1 (suc l) lc)
calls-blocks (Iter b) n l lb = calls-blocks b _ _ lb
calls-blocks (SigOp _)      n l _ = []
calls-blocks (Call _)      n l _ = []
calls-blocks (const fits-int _)   n l _ = []
calls-blocks (const fits-float _) n l _ = []
-- D380: the body starts with its environment's entry.
calls-blocks (curry {E} {A} b) n l lb =
  ++⁺ (tt ∷ ++⁺ (++⁺ (env-entry-cl (kind E) E A) (calls-trace' b _ (suc (suc l)) lb)) (tt ∷ []))
      (calls-blocks b _ (suc (suc l)) lb)
calls-blocks (g ∘ f) n l (lg , lf) =
  subst CLTrace (sym (blocks-layout-++ (bodies-of F) (bodies-of G)))
    (++⁺ (calls-blocks f n l lf) (calls-blocks g (bud F) (lab F) lg))
  where F = ir-to-trace' n l f
        G = ir-to-trace' (bud F) (lab F) g
calls-blocks (⟨ f , g ⟩) n l (lf , lg) =
  subst CLTrace (sym (blocks-layout-++ (bodies-of F) (bodies-of G)))
    (++⁺ (calls-blocks f (suc (suc (suc (suc n)))) l lf)
         (calls-blocks g (bud F) (lab F) lg))
  where F = ir-to-trace' (suc (suc (suc (suc n)))) l f
        G = ir-to-trace' (bud F) (lab F) g
calls-blocks (case f g) n l (lf , lg) =
  subst CLTrace (sym (blocks-layout-++ (bodies-of F) (bodies-of G)))
    (++⁺ (calls-blocks f n (suc (suc l)) lf) (calls-blocks g (bud F) (lab F) lg))
  where F = ir-to-trace' n (suc (suc l)) f
        G = ir-to-trace' (bud F) (lab F) g
calls-blocks (Cata {F} _ alg) n l la = calls-blocks alg 0 l la


ir-to-trace-lab-calls : ∀ {A B} (ir : IR A B) (l : ℕ) → LK ir → CLTrace (ir-to-trace-lab l ir)
ir-to-trace-lab-calls ir l lk = ++⁺ (calls-trace' ir 0 l lk) (tt ∷ calls-blocks ir 0 l lk)

ir-to-trace-top-calls : ∀ {A B} (ir : IR A B) → LK ir → CLTrace (link-top (ir-to-unit ir))
ir-to-trace-top-calls ir lk = ++⁺ (calls-trace' ir 0 0 lk) (tt ∷ calls-blocks ir 0 0 lk)
