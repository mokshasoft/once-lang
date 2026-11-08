-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.RefsClosed — plan 0.107 phase d, layer 2: EVERY SYMBOL A
-- FRAGMENT REFERENCES IS DEFINED IN ITS UNIT, OR IS GLOBAL.
--
-- What an emitted fragment references (`ImageSymbols.arefs`) falls in two
-- classes. LOCAL: a jump or branch names a `c-label`, a code address names a
-- block entry — and in both cases the emitter puts the definition in the SAME
-- unit (the fragment's trace, or the blocks it lays out). GLOBAL: a direct call
-- names a table entry, a SigOp call names an arith block or an interpretation
-- symbol — those are the program's business, collected at the IR's leaves as
-- `NodesOK`.
--
-- So the statement is MONOTONE in the set `D` of defined symbols: whatever
-- `D` contains the unit's own definitions (`Defd`), it contains every local
-- reference. That is what makes it compose — a composite fragment hands each
-- child the same `D`, and its own local references point into its own text.
--
-- THE SHAPE is `ThunkScope`'s: one clause per `ir-to-trace'` clause, the cata
-- skeletons and the compile-time functor walks as sub-lemmas.
------------------------------------------------------------------------

open import Once.Spec.Name using (CanonicalName)

module Once.CCC.Codegen.RefsClosed (o : CanonicalName) where

open import Data.Nat using (ℕ; suc; _+_; _*_; _⊔_; _∸_)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Properties using (++-assoc)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ; ∈-++⁻)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.All.Properties using (++⁺)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.String using (String)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_])
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import Once.CCC.Label using (LabelId; once; labelSym; thunkSym; ℓ)
open import Once.SigOp.Info using (SigOpInfo; module SigOpInfo)
open SigOpInfo using (sem)
open import Once.Arith.CmpOp using (CmpOp)
open import Once.Arith.SigOp.Compare using (cmp-of)
open import Once.IR using (IR)
import Once.IR as IRm
open IRm.IR
open import Once.IRTy using (⌈_⌉F; fits-int; fits-float)
open import Once.CCC.Machine.SMCore
open import Once.CCC.Codegen.ImageSymbols using (instr-defs; instr-refs; arefs)
import Once.CCC.Codegen.NodesOK
open Once.CCC.Codegen.NodesOK using (sigop-syms)
open import Once.CCC.Codegen.IRToTrace o using
  (sigop-code; ir-to-trace'; cata-dispatch; cata-strategy; CataStrategy;
   strat-const; strat-box; strat-branching; lsize; fsize; cata-body; cata-call-setup; cata-call; cata-call-box; in-trace; with-copy; two-cell; node-copy-trace; out-trace;
   cata-br-I₁; cata-br-I₂; visit-walk; rebuild-walk; wrap-sum; resuspend-layer;
   cata-call-from; inj-trace; env-entry; getμ; push2)
open import Once.CCC.Codegen.FlatLayout using (Kind; word; flat; put; put-k; get; get-k; kind; lkind; lsz;
  put-All; put-k-All; get-All; get-k-All; fill; fill-All)
open import Once.CCC.Codegen.Size using (size)
open import Once.IRTy using (IRTy; IRFunctor; ⟦_⟧TI; ν-type) renaming (_*_ to _*ᵀ_; _+_ to _+ᵀ_)
open import Once.CCC.Codegen.LabelScope o using (trace-of; cata-trace-of)
open import Once.CCC.Machine.MuRep using (MuRep; mu-box; mu-unit; mu-ptr; mu-rep)
open import Once.IRTy using (WellFormedFI; wf-K; wf-Id; wf-Sum; wf-Prod)
open import Once.Spec.Type using (K; Id; _⊕_; _⊗_)
open import Once.Spec.Type using (Fun)
open import Once.CCC.Codegen.SlotBudget o using (bodies-of)

------------------------------------------------------------------------
-- Instruction-list inclusion.
------------------------------------------------------------------------

infix 4 _⊆_
_⊆_ : AbstractTrace → AbstractTrace → Set
a ⊆ b = ∀ {i} → i ∈ a → i ∈ b

⊆-trans : ∀ {a b c} → a ⊆ b → b ⊆ c → a ⊆ c
⊆-trans p q m = q (p m)

⊆-++ˡ : ∀ (a b : AbstractTrace) → a ⊆ a ++ b
⊆-++ˡ a b = ∈-++⁺ˡ

⊆-++ʳ : ∀ (a b : AbstractTrace) → b ⊆ a ++ b
⊆-++ʳ a b = ∈-++⁺ʳ a

⊆-∷ : ∀ (i : AbstractInstr) (t : AbstractTrace) → t ⊆ i ∷ t
⊆-∷ i t = there

++-⊆ : ∀ (a b : AbstractTrace) {c} → a ⊆ c → b ⊆ c → a ++ b ⊆ c
++-⊆ a b p q m = [ p , q ] (∈-++⁻ a m)

------------------------------------------------------------------------
-- The two layout equations every composite clause needs.
------------------------------------------------------------------------

layout-++⁻ : ∀ (bs cs : List (LabelId × ℕ × AbstractTrace))
           → blocks-layout bs ++ blocks-layout cs ⊆ blocks-layout (bs ++ cs)
layout-++⁻ bs cs m = subst (_ ∈_) (sym (blocks-layout-++ bs cs)) m

arefs-++ : ∀ (a b : AbstractTrace) → arefs (a ++ b) ≡ arefs a ++ arefs b
arefs-++ []       b = refl
arefs-++ (i ∷ is) b = trans (cong (instr-refs i ++_) (arefs-++ is b))
                            (sym (++-assoc (instr-refs i) (arefs is) (arefs b)))

------------------------------------------------------------------------
-- plan 0.123 B.4 α: THE LAYOUT CODE REFERENCES NOTHING. `put`/`get` and the
-- straight rows around them name no symbol, whatever the type — stated per
-- instruction, so a trace whose length depends on a type still closes.
------------------------------------------------------------------------

NoRef : AbstractTrace → Set
NoRef = All (λ i → instr-refs i ≡ [])

put-noref : ∀ X s b o′ → NoRef (put X s b o′)
put-noref X s b o′ = put-All X s b o′ refl refl refl (λ _ → refl) (λ _ → refl)

put-k-noref : ∀ kd n s b o′ → NoRef (put-k kd n s b o′)
put-k-noref kd n s b o′ = put-k-All kd n s b o′ refl refl refl (λ _ → refl) (λ _ → refl)

get-noref : ∀ X k → NoRef (get X k)
get-noref X k = get-All X k (λ _ → refl) (λ _ → refl) refl

get-k-noref : ∀ kd n k → NoRef (get-k kd n k)
get-k-noref kd n k = get-k-All kd n k (λ _ → refl) (λ _ → refl) refl

getμ-noref : ∀ G k → NoRef (getμ G k)
getμ-noref G k = get-k-noref (lkind G word) (lsz G 1) k

fill-noref : ∀ from c → NoRef (fill from c)
fill-noref from c = fill-All from c refl (λ _ → refl)

wrap-noref : ∀ tag pk ps ss s → NoRef (wrap-sum tag pk ps ss s)
wrap-noref tag pk ps ss s =
  refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ ++⁺ (fill-noref _ (ss ∸ suc ps)) (++⁺ (put-k-noref pk ps s (suc s) 1) (refl ∷ []))

inj-noref : ∀ t P S n → NoRef (inj-trace t P S n)
inj-noref t P S n =
  refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ ++⁺ (fill-noref _ (size S ∸ suc (size P))) (++⁺ (put-noref P n (suc n) 1) (refl ∷ []))

call-noref : ∀ i0 E lk ls cl k ev pr → instr-refs i0 ≡ [] → NoRef (cata-call-from i0 E lk ls cl k ev pr)
call-noref i0 E lk ls cl k ev pr e0 =
  e0 ∷ refl ∷ refl ∷ refl ∷
  ++⁺ (put-noref E ev pr 0)
      (++⁺ (put-k-noref lk ls k pr (size E)) (refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ []))

entry-noref : ∀ kd E A → NoRef (proj₂ (env-entry kd E A))
entry-noref word E A = []
entry-noref flat E A =
  refl ∷ refl ∷ refl ∷ refl ∷ refl ∷
  ++⁺ (get-noref A 1)
      (refl ∷ refl ∷ refl ∷
       ++⁺ (put-noref E 1 3 0) (++⁺ (put-noref A 2 3 (size E)) (refl ∷ refl ∷ [])))

------------------------------------------------------------------------
-- The context: what counts as GLOBAL, and the leaf obligations.
------------------------------------------------------------------------

module _ (G : String → Set) where

  open Once.CCC.Codegen.NodesOK using (NodesOK)
  private NOK = NodesOK G

  -- every reference resolved: defined (in `D`) or global
  Closes : List String → AbstractTrace → Set
  Closes D t = All (λ s → s ∈ D ⊎ G s) (arefs t)

  closes-++ : ∀ {D} (a b : AbstractTrace) → Closes D a → Closes D b → Closes D (a ++ b)
  closes-++ a b ca cb = subst (All _) (sym (arefs-++ a b)) (++⁺ ca cb)

  noref-closes : ∀ {D} (t : AbstractTrace) → NoRef t → Closes D t
  noref-closes []      []       = []
  noref-closes {D} (i ∷ t) (e ∷ es) =
    subst (λ r → All (λ s → s ∈ D ⊎ G s) (r ++ arefs t)) (sym e) (noref-closes t es)

  -- every instruction of `t` has its definitions in `D`
  Defd : List String → AbstractTrace → Set
  Defd D t = ∀ {i} → i ∈ t → ∀ {s} → s ∈ instr-defs i → s ∈ D

  defd-⊆ : ∀ {D a b} → a ⊆ b → Defd D b → Defd D a
  defd-⊆ p d m = d (p m)

  lab∈ : ∀ {D t} (m : LabelId) → Defd D t → instr-ctrl (c-label m) ∈ t → labelSym (once m) ∈ D
  lab∈ m d mem = d mem (here refl)

  thk∈ : ∀ {D t} (m : LabelId) {b : ℕ} → Defd D t → instr-ctrl (c-thunk m b) ∈ t → thunkSym m ∈ D
  thk∈ m d mem = d mem (here refl)

  ------------------------------------------------------------------------
  -- THE CATA SKELETONS. Each strategy is the call setup, its loop fragments,
  -- the calls and ONE `cata-body` holding the algebra `at`. Every local
  -- reference — a loop's jumps, the setup's code address of the body — points
  -- at a definition in the same skeleton, located by its inclusion path.
  -- plan 0.123 B.4 α: the layout code between them references nothing
  -- (`NoRef`), whatever its length.
  ------------------------------------------------------------------------

  at⊆body : ∀ (bl el bb : ℕ) (at : AbstractTrace) → at ⊆ cata-body bl el bb at
  at⊆body bl el bb at m = there (there (∈-++⁺ˡ m))

  body-closes : ∀ {D} (bl el bb : ℕ) (at : AbstractTrace)
              → Defd D (cata-body bl el bb at) → Closes D at → Closes D (cata-body bl el bb at)
  body-closes bl el bb at d cat =
    inj₁ (lab∈ (ℓ o el) d (there (there (∈-++⁺ʳ at (there (here refl)))))) ∷
    closes-++ at (instr-ctrl (c-ret bb) ∷ instr-ctrl (c-label (ℓ o el)) ∷ []) cat []

  setup-closes : ∀ {D} (E : IRTy) (cl k ev bl : ℕ) → thunkSym (ℓ o bl) ∈ D → Closes D (cata-call-setup E cl k ev bl)
  setup-closes E cl k ev bl h = closes-++ (get E 0) _ (noref-closes (get E 0) (get-noref E 0)) (inj₁ h ∷ [])

  ------------------------------------------------------------------------
  -- THE COMPILE-TIME FUNCTOR WALKS. A `⊕` level owns `lb` and `suc lb`: it
  -- branches to `lb` and jumps to `suc lb`, and defines both itself.
  ------------------------------------------------------------------------
  visit-closes : ∀ (todo tv tb : ℕ) (F : Fun 0) (s lb : ℕ) {D}
               → Defd D (visit-walk todo tv tb F s lb) → Closes D (visit-walk todo tv tb F s lb)
  visit-closes todo tv tb (K _)   s lb d = []
  visit-closes todo tv tb Id      s lb d = []
  visit-closes todo tv tb (F ⊕ G) s lb {D} d =
    inj₁ (lab∈ (ℓ o lb) d lb∈) ∷
    closes-++ gG (mov-to-input ∷ VG ++ tailG) (noref-closes gG (getμ-noref G 1))
      (closes-++ VG tailG (visit-closes todo tv tb G (s + 4) (suc (suc lb) + lsize F) (defd-⊆ VG⊆ d))
        (inj₁ (lab∈ (ℓ o (suc lb)) d slb∈) ∷
         closes-++ gF tailF (noref-closes gF (getμ-noref F 1))
           (closes-++ VF (instr-ctrl (c-label (ℓ o (suc lb))) ∷ []) (visit-closes todo tv tb F (s + 4) (suc (suc lb)) (defd-⊆ VF⊆ d)) [])))
    where
      tailF tailG : AbstractTrace
      tailF = mov-to-input ∷ visit-walk todo tv tb F (s + 4) (suc (suc lb)) ++ (instr-ctrl (c-label (ℓ o (suc lb))) ∷ [])
      tailG = instr-ctrl (c-jmp (ℓ o (suc lb))) ∷ instr-ctrl (c-label (ℓ o lb)) ∷ getμ F 1 ++ tailF
      gG = getμ G 1
      gF = getμ F 1
      VG = visit-walk todo tv tb G (s + 4) (suc (suc lb) + lsize F)
      VF = visit-walk todo tv tb F (s + 4) (suc (suc lb))
      W = visit-walk todo tv tb (F ⊕ G) s lb
      lb∈ : instr-ctrl (c-label (ℓ o lb)) ∈ W
      lb∈ = there (∈-++⁺ʳ gG (there (∈-++⁺ʳ VG (there (here refl)))))
      slb∈ : instr-ctrl (c-label (ℓ o (suc lb))) ∈ W
      slb∈ = there (∈-++⁺ʳ gG (there (∈-++⁺ʳ VG (there (there (∈-++⁺ʳ gF (there (∈-++⁺ʳ VF (here refl)))))))))
      VG⊆ : VG ⊆ W
      VG⊆ m = there (∈-++⁺ʳ gG (there (∈-++⁺ˡ m)))
      VF⊆ : VF ⊆ W
      VF⊆ m = there (∈-++⁺ʳ gG (there (∈-++⁺ʳ VG (there (there (∈-++⁺ʳ gF (there (∈-++⁺ˡ m))))))))
  visit-closes todo tv tb (F ⊗ G) s lb {D} d =
    closes-++ gF _ (noref-closes gF (getμ-noref F 0))
      (closes-++ VF _ (visit-closes todo tv tb F (s + 4) lb (defd-⊆ VF⊆ d))
        (closes-++ gG _ (noref-closes gG (getμ-noref G (lsz F 1)))
          (visit-closes todo tv tb G (s + 4) (lb + lsize F) (defd-⊆ VG⊆ d))))
    where
      gF = getμ F 0
      gG = getμ G (lsz F 1)
      VF = visit-walk todo tv tb F (s + 4) lb
      VG = visit-walk todo tv tb G (s + 4) (lb + lsize F)
      W = visit-walk todo tv tb (F ⊗ G) s lb
      VF⊆ : VF ⊆ W
      VF⊆ m = there (there (∈-++⁺ʳ gF (there (∈-++⁺ˡ m))))
      VG⊆ : VG ⊆ W
      VG⊆ m = there (there (∈-++⁺ʳ gF (there (∈-++⁺ʳ VF (there (∈-++⁺ʳ gG (there m)))))))

  rebuild-closes : ∀ (val tv tb : ℕ) (ck : Kind) (cs : ℕ) (F : Fun 0) (s lb : ℕ) {D}
                 → Defd D (rebuild-walk val tv tb ck cs F s lb) → Closes D (rebuild-walk val tv tb ck cs F s lb)
  rebuild-closes val tv tb ck cs (K _)   s lb d = []
  rebuild-closes val tv tb ck cs Id      s lb d = []
  rebuild-closes val tv tb ck cs (F ⊕ G) s lb {D} d =
    inj₁ (lab∈ (ℓ o lb) d lb∈) ∷
    closes-++ gG _ (noref-closes gG (getμ-noref G 1))
      (closes-++ RG _ (rebuild-closes val tv tb ck cs G (s + 4) (suc (suc lb) + lsize F) (defd-⊆ RG⊆ d))
        (closes-++ WG _ (noref-closes WG (wrap-noref 1 (lkind G ck) (lsz G cs) (lsz (F ⊕ G) cs) s))
          (inj₁ (lab∈ (ℓ o (suc lb)) d slb∈) ∷
           closes-++ gF _ (noref-closes gF (getμ-noref F 1))
             (closes-++ RF _ (rebuild-closes val tv tb ck cs F (s + 4) (suc (suc lb)) (defd-⊆ RF⊆ d))
               (closes-++ WF _ (noref-closes WF (wrap-noref 0 (lkind F ck) (lsz F cs) (lsz (F ⊕ G) cs) s)) [])))))
    where
      gG = getμ G 1
      gF = getμ F 1
      RG = rebuild-walk val tv tb ck cs G (s + 4) (suc (suc lb) + lsize F)
      RF = rebuild-walk val tv tb ck cs F (s + 4) (suc (suc lb))
      WG = wrap-sum 1 (lkind G ck) (lsz G cs) (lsz (F ⊕ G) cs) s
      WF = wrap-sum 0 (lkind F ck) (lsz F cs) (lsz (F ⊕ G) cs) s
      W = rebuild-walk val tv tb ck cs (F ⊕ G) s lb
      lb∈ : instr-ctrl (c-label (ℓ o lb)) ∈ W
      lb∈ = there (∈-++⁺ʳ gG (there (∈-++⁺ʳ RG (∈-++⁺ʳ WG (there (here refl))))))
      slb∈ : instr-ctrl (c-label (ℓ o (suc lb))) ∈ W
      slb∈ = there (∈-++⁺ʳ gG (there (∈-++⁺ʳ RG (∈-++⁺ʳ WG (there (there (∈-++⁺ʳ gF (there (∈-++⁺ʳ RF (∈-++⁺ʳ WF (here refl)))))))))))
      RG⊆ : RG ⊆ W
      RG⊆ m = there (∈-++⁺ʳ gG (there (∈-++⁺ˡ m)))
      RF⊆ : RF ⊆ W
      RF⊆ m = there (∈-++⁺ʳ gG (there (∈-++⁺ʳ RG (∈-++⁺ʳ WG (there (there (∈-++⁺ʳ gF (there (∈-++⁺ˡ m)))))))))
  rebuild-closes val tv tb ck cs (F ⊗ G) s lb {D} d =
    closes-++ gG _ (noref-closes gG (getμ-noref G (lsz F 1)))
      (closes-++ RG _ (rebuild-closes val tv tb ck cs G (s + 4) (lb + lsize F) (defd-⊆ RG⊆ d))
        (closes-++ gF _ (noref-closes gF (getμ-noref F 0))
          (closes-++ RF _ (rebuild-closes val tv tb ck cs F (s + 4) lb (defd-⊆ RF⊆ d))
            (closes-++ PF _ (noref-closes PF (put-k-noref (lkind F ck) (lsz F cs) (suc s) (s + 3) 0))
              (closes-++ PG _ (noref-closes PG (put-k-noref (lkind G ck) (lsz G cs) (s + 2) (s + 3) (lsz F cs))) [])))))
    where
      gG = getμ G (lsz F 1)
      gF = getμ F 0
      RG = rebuild-walk val tv tb ck cs G (s + 4) (lb + lsize F)
      RF = rebuild-walk val tv tb ck cs F (s + 4) lb
      PF = put-k (lkind F ck) (lsz F cs) (suc s) (s + 3) 0
      PG = put-k (lkind G ck) (lsz G cs) (s + 2) (s + 3) (lsz F cs)
      W = rebuild-walk val tv tb ck cs (F ⊗ G) s lb
      RG⊆ : RG ⊆ W
      RG⊆ m = there (there (∈-++⁺ʳ gG (there (∈-++⁺ˡ m))))
      RF⊆ : RF ⊆ W
      RF⊆ m = there (there (∈-++⁺ʳ gG (there (∈-++⁺ʳ RG (there (there (∈-++⁺ʳ gF (there (∈-++⁺ˡ m)))))))))

  ------------------------------------------------------------------------
  -- THE RE-SUSPENSION PASS (D199): its code addresses name the `Ana` block
  -- (`lbl`, which the caller has defined); its `⊕` levels are `case`'s.
  ------------------------------------------------------------------------
  resusp-closes : ∀ (H : IRFunctor) (E A : IRTy) (n l : ℕ) (lbl : LabelId) (env : ℕ) {F} (wf : WellFormedFI F) {D}
                → thunkSym lbl ∈ D
                → Defd D (proj₂ (proj₂ (resuspend-layer H E A n l lbl env wf)))
                → Closes D (proj₂ (proj₂ (resuspend-layer H E A n l lbl env wf)))
  resusp-closes H E A n l lbl env (wf-K _) h d = []
  resusp-closes H E A n l lbl env wf-Id    h d =
    closes-++ (get E 0) _ (noref-closes (get E 0) (get-noref E 0))
      (closes-++ pE _ (noref-closes pE (put-noref E (suc n) (suc (suc n)) 0))
        (closes-++ pA _ (noref-closes pA (put-noref A n (suc (suc n)) (size E))) (inj₁ h ∷ [])))
    where
      pE = put E (suc n) (suc (suc n)) 0
      pA = put A n (suc (suc n)) (size E)
  resusp-closes H E A n l lbl env (wf-Prod {F} {G} wfF wfG) h d =
    closes-++ gF _ (noref-closes gF (get-noref (⟦ F ⟧TI A) 0))
      (closes-++ tF _ (resusp-closes H E A (suc (suc (suc (suc n)))) l lbl env wfF h (defd-⊆ tF⊆ d))
        (closes-++ gG _ (noref-closes gG (get-noref (⟦ G ⟧TI A) (size (⟦ F ⟧TI A))))
          (closes-++ tG _ (resusp-closes H E A (proj₁ RF) (proj₁ (proj₂ RF)) lbl env wfG h (defd-⊆ tG⊆ d))
            (closes-++ pF _ (noref-closes pF (put-noref (⟦ F ⟧TI (ν-type H)) (suc (suc n)) (suc n) 0))
              (closes-++ pG _ (noref-closes pG (put-noref (⟦ G ⟧TI (ν-type H)) (suc (suc (suc n))) (suc n)
                                                  (size (⟦ F ⟧TI (ν-type H))))) [])))))
    where
      RF = resuspend-layer H E A (suc (suc (suc (suc n)))) l lbl env wfF
      tF = proj₂ (proj₂ RF)
      tG = proj₂ (proj₂ (resuspend-layer H E A (proj₁ RF) (proj₁ (proj₂ RF)) lbl env wfG))
      gF = get (⟦ F ⟧TI A) 0
      gG = get (⟦ G ⟧TI A) (size (⟦ F ⟧TI A))
      pF = put (⟦ F ⟧TI (ν-type H)) (suc (suc n)) (suc n) 0
      pG = put (⟦ G ⟧TI (ν-type H)) (suc (suc (suc n))) (suc n) (size (⟦ F ⟧TI (ν-type H)))
      W = proj₂ (proj₂ (resuspend-layer H E A n l lbl env (wf-Prod wfF wfG)))
      tF⊆ : tF ⊆ W
      tF⊆ m = there (there (∈-++⁺ʳ gF (∈-++⁺ˡ m)))
      tG⊆ : tG ⊆ W
      tG⊆ m = there (there (∈-++⁺ʳ gF (∈-++⁺ʳ tF (there (there (∈-++⁺ʳ gG (∈-++⁺ˡ m)))))))
  resusp-closes H E A n l lbl env (wf-Sum {F} {G} wfF wfG) h d =
    inj₁ (lab∈ (ℓ o l) d inl∈) ∷
    closes-++ armG _ (arm-closes G tG 1 (resusp-closes H E A (proj₁ RF) (proj₁ (proj₂ RF)) lbl env wfG h (defd-⊆ tG⊆ d)))
      (inj₁ (lab∈ (ℓ o (suc l)) d end∈) ∷
       closes-++ armF _ (arm-closes F tF 0 (resusp-closes H E A (suc (suc (suc n))) (suc (suc l)) lbl env wfF h (defd-⊆ tF⊆ d))) [])
    where
      RF = resuspend-layer H E A (suc (suc (suc n))) (suc (suc l)) lbl env wfF
      tF = proj₂ (proj₂ RF)
      tG = proj₂ (proj₂ (resuspend-layer H E A (proj₁ RF) (proj₁ (proj₂ RF)) lbl env wfG))
      sz = size (⟦ F ⟧TI (ν-type H) +ᵀ ⟦ G ⟧TI (ν-type H))
      arm : IRFunctor → AbstractTrace → ℕ → AbstractTrace
      arm P t tag = (restore-input n ∷ []) ++ get (⟦ P ⟧TI A) 1 ++ t ++
                    (store-at-slot (suc (suc n)) ∷ instr-alloc-heap (2 ⊔ sz) ∷ store-at-slot (suc n) ∷
                     mov-to-input ∷ instr-load-tag-lit tag ∷ store-at 0 ∷ []) ++
                    fill (suc (size (⟦ P ⟧TI (ν-type H)))) (sz ∸ suc (size (⟦ P ⟧TI (ν-type H)))) ++
                    put (⟦ P ⟧TI (ν-type H)) (suc (suc n)) (suc n) 1 ++
                    (load-from-slot (suc n) ∷ [])
      armG = arm G tG 1
      armF = arm F tF 0
      arm-closes : ∀ {D′} (P : IRFunctor) (t : AbstractTrace) (tag : ℕ) → Closes D′ t → Closes D′ (arm P t tag)
      arm-closes P t tag ct =
        closes-++ (get (⟦ P ⟧TI A) 1) _ (noref-closes (get (⟦ P ⟧TI A) 1) (get-noref (⟦ P ⟧TI A) 1))
          (closes-++ t _ ct
            (closes-++ (fill (suc (size (⟦ P ⟧TI (ν-type H)))) (sz ∸ suc (size (⟦ P ⟧TI (ν-type H))))) _
               (noref-closes (fill (suc (size (⟦ P ⟧TI (ν-type H)))) (sz ∸ suc (size (⟦ P ⟧TI (ν-type H))))) (fill-noref _ _))
               (closes-++ (put (⟦ P ⟧TI (ν-type H)) (suc (suc n)) (suc n) 1) _
                  (noref-closes (put (⟦ P ⟧TI (ν-type H)) (suc (suc n)) (suc n) 1)
                                (put-noref (⟦ P ⟧TI (ν-type H)) (suc (suc n)) (suc n) 1)) [])))
      W = proj₂ (proj₂ (resuspend-layer H E A n l lbl env (wf-Sum wfF wfG)))
      inl∈ : instr-ctrl (c-label (ℓ o l)) ∈ W
      inl∈ = there (there (there (∈-++⁺ʳ armG (there (here refl)))))
      end∈ : instr-ctrl (c-label (ℓ o (suc l))) ∈ W
      end∈ = there (there (there (∈-++⁺ʳ armG (there (there (∈-++⁺ʳ armF (here refl)))))))
      tG⊆ : tG ⊆ W
      tG⊆ m = there (there (there (∈-++⁺ˡ (there (∈-++⁺ʳ (get (⟦ G ⟧TI A) 1) (∈-++⁺ˡ m))))))
      tF⊆ : tF ⊆ W
      tF⊆ m = there (there (there (∈-++⁺ʳ armG (there (there (∈-++⁺ˡ (there (∈-++⁺ʳ (get (⟦ F ⟧TI A) 1) (∈-++⁺ˡ m)))))))))

  module BrS (E A : IRTy) (F : Fun 0) (bb n1 l1 : ℕ) (at : AbstractTrace) where
    Lb = l1 + 4 + lsize F + lsize F
    B0 = n1 + 7 + (4 * fsize F) + 4
    S = cata-call-setup E B0 (B0 + 1) (B0 + 2) Lb
    C = cata-call E (lkind F (kind A)) (lsz F (size A)) B0 (B0 + 1) (B0 + 2) (B0 + 3)
    B = cata-body Lb (Lb + 1) bb at
    I₁ = cata-br-I₁ (kind A) (size A) F n1 l1
    I₂ = cata-br-I₂ n1 l1
    T  = S ++ (I₁ ++ (C ++ (I₂ ++ B)))
    I₁⊆ : I₁ ⊆ T
    I₁⊆ m = ∈-++⁺ʳ S (∈-++⁺ˡ m)
    I₂⊆ : I₂ ⊆ T
    I₂⊆ m = ∈-++⁺ʳ S (∈-++⁺ʳ I₁ (∈-++⁺ʳ C (∈-++⁺ˡ m)))
    B⊆ : B ⊆ T
    B⊆ m = ∈-++⁺ʳ S (∈-++⁺ʳ I₁ (∈-++⁺ʳ C (∈-++⁺ʳ I₂ m)))
    VW = visit-walk n1 (n1 + 4) (n1 + 5) F (n1 + 7) (l1 + 4)
    RW = rebuild-walk (n1 + 2) (n1 + 4) (n1 + 5) (kind A) (size A) F (n1 + 7) (l1 + 4 + lsize F)
    -- the init/flatten rows before the visit walk are 46 concrete rows
    VW⊆ : VW ⊆ I₁
    VW⊆ m = (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (∈-++⁺ˡ m)))))))))))))))))))))))))))))))))))))))))))))))
    RW⊆ : RW ⊆ I₁
    RW⊆ m = (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (∈-++⁺ʳ VW (there (there (there (there (there (there (there (there (there (there (∈-++⁺ˡ m))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    sl1∈ : instr-ctrl (c-label (ℓ o (suc l1))) ∈ I₁
    sl1∈ = (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (∈-++⁺ʳ VW (there (here refl)))))))))))))))))))))))))))))))))))))))))))))))))
    l1∈ : instr-ctrl (c-label (ℓ o l1)) ∈ I₁
    l1∈ = (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (here refl)))))))))))))))))))))))))
    l2∈ : instr-ctrl (c-label (ℓ o (l1 + 2))) ∈ I₁
    l2∈ = (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (∈-++⁺ʳ VW (there (there (here refl))))))))))))))))))))))))))))))))))))))))))))))))))
    l3∈ : instr-ctrl (c-label (ℓ o (l1 + 3))) ∈ I₂
    l3∈ = (there (there (there (there (there (there (there (there (there (there (there (here refl))))))))))))
    closes : ∀ {D} → Defd D T → Closes D at → Closes D T
    closes d cat =
      closes-++ S _ (setup-closes E B0 (B0 + 1) (B0 + 2) Lb (thk∈ (ℓ o Lb) d (B⊆ (there (here refl)))))
        (closes-++ I₁ _
          (inj₁ (lab∈ (ℓ o (suc l1)) d (I₁⊆ sl1∈)) ∷
           closes-++ VW _ (visit-closes n1 (n1 + 4) (n1 + 5) F (n1 + 7) (l1 + 4) (defd-⊆ (⊆-trans VW⊆ I₁⊆) d))
             (inj₁ (lab∈ (ℓ o l1) d (I₁⊆ l1∈)) ∷
              inj₁ (lab∈ (ℓ o (l1 + 3)) d (I₂⊆ l3∈)) ∷
              closes-++ RW _ (rebuild-closes (n1 + 2) (n1 + 4) (n1 + 5) (kind A) (size A) F (n1 + 7) (l1 + 4 + lsize F)
                                (defd-⊆ (⊆-trans RW⊆ I₁⊆) d)) []))
          (closes-++ C _ (noref-closes C (call-noref mov-to-output E (lkind F (kind A)) (lsz F (size A))
                                            B0 (B0 + 1) (B0 + 2) (B0 + 3) refl))
            (closes-++ I₂ B (inj₁ (lab∈ (ℓ o (l1 + 2)) d (I₁⊆ l2∈)) ∷ [])
              (body-closes Lb (Lb + 1) bb at (defd-⊆ B⊆ d) cat))))

  at⊆ : ∀ (E A : IRTy) (G : Fun 0) (st : CataStrategy) (bb n1 l1 : ℕ) (at : AbstractTrace)
      → at ⊆ cata-trace-of (cata-dispatch E A G st bb n1 l1 at)
  cata-closes : ∀ (E A : IRTy) (G : Fun 0) (st : CataStrategy) (bb n1 l1 : ℕ) (at : AbstractTrace) {D}
              → Defd D (cata-trace-of (cata-dispatch E A G st bb n1 l1 at)) → Closes D at
              → Closes D (cata-trace-of (cata-dispatch E A G st bb n1 l1 at))

  at⊆ E A G strat-const bb n1 l1 at =
    ⊆-trans (at⊆body l1 (l1 + 1) bb at)
      (⊆-trans (⊆-++ʳ (cata-call E (lkind G word) (lsz G 1) n1 (n1 + 1) (n1 + 2) (n1 + 3)) (cata-body l1 (l1 + 1) bb at))
               (⊆-++ʳ (cata-call-setup E n1 (n1 + 1) (n1 + 2) l1) _))
  at⊆ E A G strat-box bb n1 l1 at =
    ⊆-trans (at⊆body l1 (l1 + 1) bb at)
      (⊆-trans (⊆-++ʳ (cata-call-box E (lkind G word) (lsz G 1) n1 (n1 + 1) (n1 + 2) (n1 + 3)) (cata-body l1 (l1 + 1) bb at))
               (⊆-++ʳ (cata-call-setup E n1 (n1 + 1) (n1 + 2) l1) _))
  at⊆ E A G (strat-branching F) bb n1 l1 at = ⊆-trans (at⊆body _ _ bb at) (BrS.B⊆ E A F bb n1 l1 at)

  cata-closes E A G strat-const bb n1 l1 at {D} d cat =
    closes-++ S (C ++ B) (setup-closes E n1 (n1 + 1) (n1 + 2) l1 (thk∈ (ℓ o l1) d (B⊆T (there (here refl)))))
      (closes-++ C B (noref-closes C (call-noref mov-to-output E (lkind G word) (lsz G 1) n1 (n1 + 1) (n1 + 2) (n1 + 3) refl))
                     (body-closes l1 (l1 + 1) bb at (defd-⊆ B⊆T d) cat))
    where
      S = cata-call-setup E n1 (n1 + 1) (n1 + 2) l1
      C = cata-call E (lkind G word) (lsz G 1) n1 (n1 + 1) (n1 + 2) (n1 + 3)
      B = cata-body l1 (l1 + 1) bb at
      B⊆T : B ⊆ S ++ (C ++ B)
      B⊆T = ⊆-trans (⊆-++ʳ C B) (⊆-++ʳ S (C ++ B))
  cata-closes E A G strat-box bb n1 l1 at {D} d cat =
    closes-++ S (C ++ B) (setup-closes E n1 (n1 + 1) (n1 + 2) l1 (thk∈ (ℓ o l1) d (B⊆T (there (here refl)))))
      (closes-++ C B (noref-closes C (call-noref (load-at 0) E (lkind G word) (lsz G 1) n1 (n1 + 1) (n1 + 2) (n1 + 3) refl))
                     (body-closes l1 (l1 + 1) bb at (defd-⊆ B⊆T d) cat))
    where
      S = cata-call-setup E n1 (n1 + 1) (n1 + 2) l1
      C = cata-call-box E (lkind G word) (lsz G 1) n1 (n1 + 1) (n1 + 2) (n1 + 3)
      B = cata-body l1 (l1 + 1) bb at
      B⊆T : B ⊆ S ++ (C ++ B)
      B⊆T = ⊆-trans (⊆-++ʳ C B) (⊆-++ʳ S (C ++ B))
  cata-closes E A G (strat-branching F) bb n1 l1 at {D} d cat = BrS.closes E A F bb n1 l1 at d cat

  ------------------------------------------------------------------------
  -- THE INDUCTION.
  ------------------------------------------------------------------------

  Unit : ℕ × ℕ × AbstractTrace × List (LabelId × ℕ × AbstractTrace) → AbstractTrace
  Unit X = trace-of X ++ blocks-layout (bodies-of X)

  sigop-closes : ∀ {A B D} (si : SigOpInfo A B) (n : ℕ) (m : Maybe CmpOp)
               → All G (sigop-syms si m) → Closes D (sigop-code si n m)
  sigop-closes si n nothing  (g ∷ []) = inj₂ g ∷ []
  sigop-closes si n (just c) (g ∷ []) = inj₂ g ∷ []

  -- D366: `In`'s three shapes and `out-μ`'s reference nothing.
  in-closes : ∀ {D} (r : MuRep) kd L (n : ℕ) → Closes D (in-trace r kd L n)
  in-closes mu-box  kd L n = []
  in-closes mu-unit kd L n = []
  in-closes mu-ptr  word L n = []
  in-closes mu-ptr  flat L n = noref-closes (node-copy-trace L n) (refl ∷ refl ∷ refl ∷ refl ∷ ++⁺ (put-noref L n (suc n) 0) (refl ∷ []))

  out-closes : ∀ {D} (r : MuRep) → Closes D (out-trace r)
  out-closes mu-box  = []
  out-closes mu-unit = []
  out-closes mu-ptr  = []

  -- D399: a kept value's copy, then the two-cell build: the copy names nothing
  wc-closes : ∀ {D} kd E n c → (Closes D (two-cell 0 c)) → Closes D (with-copy kd E n (λ m → two-cell m c))
  wc-closes word E n c r = r
  wc-closes flat E n c r =
    closes-++ (node-copy-trace E n) (mov-to-input ∷ two-cell (suc (suc n)) c)
      (noref-closes (node-copy-trace E n) (refl ∷ refl ∷ refl ∷ refl ∷ ++⁺ (put-noref E n (suc n) 0) (refl ∷ []))) r

  close : ∀ {A B} (ir : IR A B) (n l : ℕ) {D}
        → Defd D (Unit (ir-to-trace' n l ir)) → NOK ir
        → Closes D (trace-of (ir-to-trace' n l ir)) × Closes D (blocks-layout (bodies-of (ir-to-trace' n l ir)))
  close id       n l d ok = [] , []
  close (fst {A} {B}) n l d ok = noref-closes (get A 0) (get-noref A 0) , []
  close (snd {A} {B}) n l d ok = noref-closes (get B (size A)) (get-noref B (size A)) , []
  close terminal n l d ok = [] , []
  close initial  n l d ok = [] , []
  close (inl {A} {B}) n l d ok = noref-closes (inj-trace 0 A (A +ᵀ B) n) (inj-noref 0 A (A +ᵀ B) n) , []
  close (inr {A} {B}) n l d ok = noref-closes (inj-trace 1 B (A +ᵀ B) n) (inj-noref 1 B (A +ᵀ B) n) , []
  close (apply {A} {B}) n l d ok =
    closes-++ (get A 1) _ (noref-closes (get A 1) (get-noref A 1))
      (closes-++ (put A n (suc (suc n)) 1) _ (noref-closes (put A n (suc (suc n)) 1) (put-noref A n (suc (suc n)) 1)) [])
    , []
  close (In {F} _)    n l d ok = in-closes (mu-rep F) _ _ n , []
  close (out-μ {F} _) n l d ok = out-closes (mu-rep F) , []
  close (Out _)   n l d ok = [] , []
  close (const fits-int   v) n l d ok = [] , []
  close (const fits-float v) n l d ok = [] , []
  close (Call f)  n l d ok = inj₂ ok ∷ [] , []
  close (SigOp si) n l d ok = sigop-closes si n (cmp-of (sem si)) ok , []
  close (g ∘ f) n l {D} d (okg , okf) =
    closes-++ ft (mov-to-input ∷ gt) (proj₁ cf) (proj₁ cg)
    , subst (Closes D) (sym (blocks-layout-++ fb gb))
            (closes-++ (blocks-layout fb) (blocks-layout gb) (proj₂ cf) (proj₂ cg))
    where
      X = ir-to-trace' n l f
      ft = trace-of X ; fb = bodies-of X
      Y = ir-to-trace' (proj₁ X) (proj₁ (proj₂ X)) g
      gt = trace-of Y ; gb = bodies-of Y
      T = ft ++ mov-to-input ∷ gt
      L = blocks-layout (fb ++ gb)
      inT : T ⊆ T ++ L
      inT = ⊆-++ˡ T L
      inL : blocks-layout fb ++ blocks-layout gb ⊆ T ++ L
      inL = ⊆-trans (layout-++⁻ fb gb) (⊆-++ʳ T L)
      cf = close f n l (defd-⊆ (++-⊆ ft (blocks-layout fb)
                                   (⊆-trans (⊆-++ˡ ft (mov-to-input ∷ gt)) inT)
                                   (⊆-trans (⊆-++ˡ (blocks-layout fb) (blocks-layout gb)) inL)) d) okf
      cg = close g (proj₁ X) (proj₁ (proj₂ X))
                 (defd-⊆ (++-⊆ gt (blocks-layout gb)
                            (⊆-trans (⊆-trans (⊆-∷ mov-to-input gt) (⊆-++ʳ ft (mov-to-input ∷ gt))) inT)
                            (⊆-trans (⊆-++ʳ (blocks-layout fb) (blocks-layout gb)) inL)) d) okg
  close (⟨_,_⟩ {A} {B} {C} f g) n l {D} d (okf , okg) =
    closes-++ ft _ (proj₁ cf)
      (closes-++ gt _ (proj₁ cg)
        (closes-++ pB _ (noref-closes pB (put-noref B (suc n) (suc (suc (suc n))) 0))
          (closes-++ pC _ (noref-closes pC (put-noref C (suc (suc n)) (suc (suc (suc n))) (size B))) [])))
    , subst (Closes D) (sym (blocks-layout-++ fb gb))
            (closes-++ (blocks-layout fb) (blocks-layout gb) (proj₂ cf) (proj₂ cg))
    where
      X = ir-to-trace' (suc (suc (suc (suc n)))) l f
      ft = trace-of X ; fb = bodies-of X
      Y = ir-to-trace' (proj₁ X) (proj₁ (proj₂ X)) g
      gt = trace-of Y ; gb = bodies-of Y
      pB = put B (suc n) (suc (suc (suc n))) 0
      pC = put C (suc (suc n)) (suc (suc (suc n))) (size B)
      T = trace-of (ir-to-trace' n l (⟨_,_⟩ {A} {B} {C} f g))
      L = blocks-layout (fb ++ gb)
      inT : T ⊆ T ++ L
      inT = ⊆-++ˡ T L
      inL : blocks-layout fb ++ blocks-layout gb ⊆ T ++ L
      inL = ⊆-trans (layout-++⁻ fb gb) (⊆-++ʳ T L)
      ftT : ft ⊆ T
      ftT m = there (there (∈-++⁺ˡ m))
      gtT : gt ⊆ T
      gtT m = there (there (∈-++⁺ʳ ft (there (there (∈-++⁺ˡ m)))))
      cf = close f (suc (suc (suc (suc n)))) l
                 (defd-⊆ (++-⊆ ft (blocks-layout fb) (⊆-trans ftT inT)
                            (⊆-trans (⊆-++ˡ (blocks-layout fb) (blocks-layout gb)) inL)) d) okf
      cg = close g (proj₁ X) (proj₁ (proj₂ X))
                 (defd-⊆ (++-⊆ gt (blocks-layout gb) (⊆-trans gtT inT)
                            (⊆-trans (⊆-++ʳ (blocks-layout fb) (blocks-layout gb)) inL)) d) okg
  close (case {A} {B} f g) n l {D} d (okf , okg) =
    inj₁ (lab∈ (ℓ o l) d inl∈) ∷
      closes-++ gB _ (noref-closes gB (get-noref B 1))
        (closes-++ gt _ (proj₁ cg)
          (inj₁ (lab∈ (ℓ o (suc l)) d end∈) ∷
           closes-++ gA _ (noref-closes gA (get-noref A 1)) (closes-++ ft _ (proj₁ cf) [])))
    , subst (Closes D) (sym (blocks-layout-++ fb gb))
            (closes-++ (blocks-layout fb) (blocks-layout gb) (proj₂ cf) (proj₂ cg))
    where
      X = ir-to-trace' n (suc (suc l)) f
      ft = trace-of X ; fb = bodies-of X
      Y = ir-to-trace' (proj₁ X) (proj₁ (proj₂ X)) g
      gt = trace-of Y ; gb = bodies-of Y
      gA = get A 1
      gB = get B 1
      T = trace-of (ir-to-trace' n l (case {A} {B} f g))
      L = blocks-layout (fb ++ gb)
      inT : T ⊆ T ++ L
      inT = ⊆-++ˡ T L
      inL : blocks-layout fb ++ blocks-layout gb ⊆ T ++ L
      inL = ⊆-trans (layout-++⁻ fb gb) (⊆-++ʳ T L)
      inl∈ : instr-ctrl (c-label (ℓ o l)) ∈ T ++ L
      inl∈ = inT (there (∈-++⁺ʳ gB (there (∈-++⁺ʳ gt (there (here refl))))))
      end∈ : instr-ctrl (c-label (ℓ o (suc l))) ∈ T ++ L
      end∈ = inT (there (∈-++⁺ʳ gB (there (∈-++⁺ʳ gt (there (there (∈-++⁺ʳ gA (there (∈-++⁺ʳ ft (here refl))))))))))
      ftT : ft ⊆ T
      ftT m = there (∈-++⁺ʳ gB (there (∈-++⁺ʳ gt (there (there (∈-++⁺ʳ gA (there (∈-++⁺ˡ m))))))))
      gtT : gt ⊆ T
      gtT m = there (∈-++⁺ʳ gB (there (∈-++⁺ˡ m)))
      cf = close f n (suc (suc l))
                 (defd-⊆ (++-⊆ ft (blocks-layout fb) (⊆-trans ftT inT)
                            (⊆-trans (⊆-++ˡ (blocks-layout fb) (blocks-layout gb)) inL)) d) okf
      cg = close g (proj₁ X) (proj₁ (proj₂ X))
                 (defd-⊆ (++-⊆ gt (blocks-layout gb) (⊆-trans gtT inT)
                            (⊆-trans (⊆-++ʳ (blocks-layout fb) (blocks-layout gb)) inL)) d) okg
  -- the loop: its two references (the exit branch, the back edge) name its own
  -- two labels; the round closes by its IH.
  close (Iter {E} {A} {B} b) n l {D} d okb =
    closes-++ gE _ (noref-closes gE (get-noref E 0))
      (closes-++ bt _ (proj₁ cb)
        (inj₁ (lab∈ (ℓ o (suc l)) d done∈) ∷
         closes-++ gA _ (noref-closes gA (get-noref A 1))
           (closes-++ pE _ (noref-closes pE (put-noref E (suc n) (suc (suc (suc n))) 0))
             (closes-++ pA _ (noref-closes pA (put-noref A (suc (suc n)) (suc (suc (suc n))) (size E)))
               (inj₁ (lab∈ (ℓ o l) d top∈) ∷ noref-closes gB (get-noref B 1))))))
    , proj₂ cb
    where
      X = ir-to-trace' (suc (suc (suc (suc n)))) (suc (suc l)) b
      bt = trace-of X ; bbs = bodies-of X
      gE = get E 0
      gA = get A 1
      gB = get B 1
      pE = put E (suc n) (suc (suc (suc n))) 0
      pA = put A (suc (suc n)) (suc (suc (suc n))) (size E)
      T = trace-of (ir-to-trace' n l (Iter {E} {A} {B} b))
      L = blocks-layout bbs
      inT : T ⊆ T ++ L
      inT = ⊆-++ˡ T L
      btT : bt ⊆ T
      btT m = ∈-++⁺ʳ gE (there (there (∈-++⁺ˡ m)))
      top∈ : instr-ctrl (c-label (ℓ o l)) ∈ T ++ L
      top∈ = inT (∈-++⁺ʳ gE (there (here refl)))
      done∈ : instr-ctrl (c-label (ℓ o (suc l))) ∈ T ++ L
      done∈ = inT (∈-++⁺ʳ gE (there (there (∈-++⁺ʳ bt (there (there (∈-++⁺ʳ gA
                (there (there (there (∈-++⁺ʳ pE (∈-++⁺ʳ pA (there (there (there (here refl))))))))))))))))
      cb = close b (suc (suc (suc (suc n)))) (suc (suc l))
                 (defd-⊆ (++-⊆ bt L (⊆-trans btT inT) (⊆-++ʳ T L)) d) okb
  close (curry {E} {A} b) n l {D} d okb =
    wc-closes (kind E) E n (ℓ o l) (inj₁ (thk∈ (ℓ o l) d thk∈U) ∷ [])
    , closes-++ (block-layout (ℓ o l , bb , bt)) (blocks-layout bbs)
                (closes-++ bt (instr-ctrl (c-ret bb) ∷ [])
                   (closes-++ pro bt₀ (noref-closes pro (entry-noref (kind E) E A)) (proj₁ cb)) [])
                (proj₂ cb)
    where
      pro = proj₂ (env-entry (kind E) E A)
      X = ir-to-trace' (proj₁ (env-entry (kind E) E A)) (suc (suc l)) b
      bb = proj₁ X ; bt₀ = trace-of X ; bbs = bodies-of X
      bt = pro ++ bt₀
      T = trace-of (ir-to-trace' n l (curry {E} {A} b))
      L = blocks-layout ((ℓ o l , bb , bt) ∷ bbs)
      thk∈U : instr-ctrl (c-thunk (ℓ o l) bb) ∈ T ++ L
      thk∈U = ∈-++⁺ʳ T (here refl)
      btU : bt₀ ⊆ T ++ L
      btU m = ∈-++⁺ʳ T (there (∈-++⁺ˡ {ys = blocks-layout bbs} (∈-++⁺ˡ (∈-++⁺ʳ pro m))))
      bbsU : blocks-layout bbs ⊆ T ++ L
      bbsU m = ∈-++⁺ʳ T (∈-++⁺ʳ (block-layout (ℓ o l , bb , bt)) m)
      cb = close b (proj₁ (env-entry (kind E) E A)) (suc (suc l)) (defd-⊆ (++-⊆ bt₀ (blocks-layout bbs) btU bbsU) d) okb
  close (in-ν {F} w) n l {D} d ok =
    wc-closes (kind (⟦ F ⟧TI (ν-type F))) _ n (ℓ o l) (inj₁ (thk∈ (ℓ o l) d (∈-++⁺ʳ (trace-of (ir-to-trace' n l (in-ν w))) (here refl))) ∷ []) , []
  close (Cata {F} w {E} {A} alg) n l {D} d ok =
    cata-closes E A ⌈ F ⌉F (cata-strategy ⌈ F ⌉F) bb n l1 at (defd-⊆ (⊆-++ˡ T L) d) (proj₁ ca)
    , proj₂ ca
    where
      X = ir-to-trace' 0 l alg
      bb = proj₁ X ; l1 = proj₁ (proj₂ X) ; at = trace-of X ; ab = bodies-of X
      T = cata-trace-of (cata-dispatch E A ⌈ F ⌉F (cata-strategy ⌈ F ⌉F) bb n l1 at)
      L = blocks-layout ab
      ca = close alg 0 l (defd-⊆ (++-⊆ at L (⊆-trans (at⊆ E A ⌈ F ⌉F (cata-strategy ⌈ F ⌉F) bb n l1 at) (⊆-++ˡ T L))
                                           (⊆-++ʳ T L)) d) ok
  close (Ana {F} wf {E} {A} c) n l {D} d ok =
    wc-closes flat (E *ᵀ A) n (ℓ o l) (inj₁ (thk∈ (ℓ o l) d (∈-++⁺ʳ T (here refl))) ∷ [])
    , closes-++ (block-layout (ℓ o l , bb , bt)) (blocks-layout cbs)
                (closes-++ bt (instr-ctrl (c-ret bb) ∷ [])
                   (closes-++ ct rt (proj₁ cc)
                      (resusp-closes F E A cb l2 (ℓ o l) 0 wf (thk∈ (ℓ o l) d (∈-++⁺ʳ T (here refl)))
                                     (defd-⊆ rtU d)))
                   [])
                (proj₂ cc)
    where
      X = ir-to-trace' 1 (suc l) c
      cb = proj₁ X ; l2 = proj₁ (proj₂ X) ; ct = trace-of X ; cbs = bodies-of X
      R = resuspend-layer F E A cb l2 (ℓ o l) 0 wf
      bb = proj₁ R ; rt = proj₂ (proj₂ R)
      -- D273: the block's prologue keeps the seed pair; it names no symbol.
      bt = mov-to-output ∷ store-at-slot 0 ∷ (ct ++ rt)
      T = trace-of (ir-to-trace' n l (Ana wf c))
      L = blocks-layout ((ℓ o l , bb , bt) ∷ cbs)
      blkU₀ : bt ⊆ T ++ L
      blkU₀ m = ∈-++⁺ʳ T (there (∈-++⁺ˡ {ys = blocks-layout cbs} (∈-++⁺ˡ m)))
      blkU : (ct ++ rt) ⊆ T ++ L
      blkU m = blkU₀ (there (there m))
      rtU : rt ⊆ T ++ L
      rtU = ⊆-trans (⊆-++ʳ ct rt) blkU
      cbsU : blocks-layout cbs ⊆ T ++ L
      cbsU m = ∈-++⁺ʳ T (∈-++⁺ʳ (block-layout (ℓ o l , bb , bt)) m)
      cc = close c 1 (suc l) (defd-⊆ (++-⊆ ct (blocks-layout cbs) (⊆-trans (⊆-++ˡ ct rt) blkU) cbsU) d) ok
