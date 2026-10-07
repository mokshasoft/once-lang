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

open import Once.CanonicalName using (CanonicalName)

module Once.CCC.Codegen.RefsClosed (o : CanonicalName) where

open import Data.Nat using (ℕ; suc; _+_; _*_)
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
open import Once.SigOp.Info using (SigOpInfo; sem)
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
   strat-const; strat-nat; strat-linear; strat-branching; lsize; fsize; cata-body; cata-call-setup; cata-call;
   cata-nat-I₁; cata-nat-I₂; cata-nat-I₃; cata-lin-I₁; cata-lin-I₂; cata-lin-I₃;
   cata-br-I₁; cata-br-I₂; visit-walk; rebuild-walk; wrap-sum; resuspend-layer)
open import Once.CCC.Codegen.LabelScope o using (trace-of; cata-trace-of)
open import Once.IRTy using (WellFormedFI; wf-K; wf-Id; wf-Sum; wf-Prod)
open import Once.Type using (Functor; K; Id; _⊕_; _⊗_)
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

layout-++ : ∀ (bs cs : List (LabelId × ℕ × AbstractTrace))
          → blocks-layout (bs ++ cs) ⊆ blocks-layout bs ++ blocks-layout cs
layout-++ bs cs m = subst (_ ∈_) (blocks-layout-++ bs cs) m

layout-++⁻ : ∀ (bs cs : List (LabelId × ℕ × AbstractTrace))
           → blocks-layout bs ++ blocks-layout cs ⊆ blocks-layout (bs ++ cs)
layout-++⁻ bs cs m = subst (_ ∈_) (sym (blocks-layout-++ bs cs)) m

arefs-++ : ∀ (a b : AbstractTrace) → arefs (a ++ b) ≡ arefs a ++ arefs b
arefs-++ []       b = refl
arefs-++ (i ∷ is) b = trans (cong (instr-refs i ++_) (arefs-++ is b))
                            (sym (++-assoc (instr-refs i) (arefs is) (arefs b)))

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
  ------------------------------------------------------------------------

  at⊆body : ∀ (bl el bb : ℕ) (at : AbstractTrace) → at ⊆ cata-body bl el bb at
  at⊆body bl el bb at m = there (there (∈-++⁺ˡ m))

  body-closes : ∀ {D} (bl el bb : ℕ) (at : AbstractTrace)
              → Defd D (cata-body bl el bb at) → Closes D at → Closes D (cata-body bl el bb at)
  body-closes bl el bb at d cat =
    inj₁ (lab∈ (ℓ o el) d (there (there (∈-++⁺ʳ at (there (here refl)))))) ∷
    closes-++ at (instr-ctrl (c-ret bb) ∷ instr-ctrl (c-label (ℓ o el)) ∷ []) cat []

  setup-closes : ∀ {D} (cl k ev pr bl : ℕ) → thunkSym (ℓ o bl) ∈ D → Closes D (cata-call-setup cl k ev pr bl)
  setup-closes cl k ev pr bl h = inj₁ h ∷ []

  -- `S ++ (I₁ ++ (C ++ (I₂ ++ (C ++ (I₃ ++ B)))))`, the shape both counted
  -- strategies share.
  module Six (S I₁ C I₂ I₃ B : AbstractTrace) where
    R₄ = I₃ ++ B
    R₃ = C ++ R₄
    R₂ = I₂ ++ R₃
    R₁ = C ++ R₂
    R₀ = I₁ ++ R₁
    T  = S ++ R₀
    R₀⊆ : R₀ ⊆ T
    R₀⊆ = ⊆-++ʳ S R₀
    I₁⊆ : I₁ ⊆ T
    I₁⊆ = ⊆-trans (⊆-++ˡ I₁ R₁) R₀⊆
    R₁⊆ : R₁ ⊆ T
    R₁⊆ = ⊆-trans (⊆-++ʳ I₁ R₁) R₀⊆
    R₂⊆ : R₂ ⊆ T
    R₂⊆ = ⊆-trans (⊆-++ʳ C R₂) R₁⊆
    I₂⊆ : I₂ ⊆ T
    I₂⊆ = ⊆-trans (⊆-++ˡ I₂ R₃) R₂⊆
    R₃⊆ : R₃ ⊆ T
    R₃⊆ = ⊆-trans (⊆-++ʳ I₂ R₃) R₂⊆
    R₄⊆ : R₄ ⊆ T
    R₄⊆ = ⊆-trans (⊆-++ʳ C R₄) R₃⊆
    I₃⊆ : I₃ ⊆ T
    I₃⊆ = ⊆-trans (⊆-++ˡ I₃ B) R₄⊆
    B⊆ : B ⊆ T
    B⊆ = ⊆-trans (⊆-++ʳ I₃ B) R₄⊆
    closes-six : ∀ {D} → Closes D S → Closes D I₁ → Closes D C → Closes D I₂ → Closes D I₃ → Closes D B → Closes D T
    closes-six cs c1 cc c2 c3 cb =
      closes-++ S R₀ cs (closes-++ I₁ R₁ c1 (closes-++ C R₂ cc (closes-++ I₂ R₃ c2
        (closes-++ C R₄ cc (closes-++ I₃ B c3 cb)))))

  module NatS where
    module _ (bb n1 l1 : ℕ) (at : AbstractTrace) where
      S = cata-call-setup (suc (suc n1)) (suc (suc (suc n1))) (suc (suc (suc (suc n1)))) (suc (suc (suc (suc (suc n1))))) (suc (suc (suc (suc (suc (suc l1))))))
      C = cata-call (suc (suc n1)) (suc (suc (suc n1))) (suc (suc (suc (suc (suc n1)))))
      B = cata-body (suc (suc (suc (suc (suc (suc l1)))))) (suc (suc (suc (suc (suc (suc (suc l1))))))) bb at
      open Six S (cata-nat-I₁ n1 l1) C (cata-nat-I₂ n1 l1) (cata-nat-I₃ l1) B public using (B⊆; I₁⊆; I₂⊆; I₃⊆; closes-six)
      closes : ∀ {D} → Defd D (cata-trace-of (cata-dispatch strat-nat bb n1 l1 at)) → Closes D at
             → Closes D (cata-trace-of (cata-dispatch strat-nat bb n1 l1 at))
      closes d cat = closes-six
        (inj₁ (thk∈ (ℓ o (suc (suc (suc (suc (suc (suc l1))))))) d (B⊆ (there (here refl)))) ∷ [])
        (inj₁ (lab∈ (ℓ o (suc l1)) d (I₁⊆ (there (there (there (there (there (there (there (there (there (there (there (there (there (here refl)))))))))))))))) ∷
         inj₁ (lab∈ (ℓ o (suc (suc l1))) d (I₁⊆ (there (there (there (there (there (there (there (there (there (here refl)))))))))))) ∷
         inj₁ (lab∈ (ℓ o (suc (suc (suc l1)))) d (I₁⊆ (there (there (there (there (there (there (there (there (there (there (there (here refl)))))))))))))) ∷
         inj₁ (lab∈ (ℓ o l1) d (I₁⊆ (there (there (here refl))))) ∷ [])
        []
        (inj₁ (lab∈ (ℓ o (suc (suc (suc (suc (suc l1)))))) d (I₃⊆ (there (there (here refl))))) ∷ [])
        (inj₁ (lab∈ (ℓ o (suc (suc (suc (suc l1))))) d (I₂⊆ (here refl))) ∷ [])
        (body-closes _ _ bb at (defd-⊆ B⊆ d) cat)
  module LinS where
    module _ (bb n1 l1 : ℕ) (at : AbstractTrace) where
      S = cata-call-setup (suc (suc (suc (suc (suc (suc n1)))))) (suc (suc (suc (suc (suc (suc (suc n1))))))) (suc (suc (suc (suc (suc (suc (suc (suc n1)))))))) (suc (suc (suc (suc (suc (suc (suc (suc (suc n1))))))))) (suc (suc (suc (suc l1))))
      C = cata-call (suc (suc (suc (suc (suc (suc n1)))))) (suc (suc (suc (suc (suc (suc (suc n1))))))) (suc (suc (suc (suc (suc (suc (suc (suc (suc n1)))))))))
      B = cata-body (suc (suc (suc (suc l1)))) (suc (suc (suc (suc (suc l1))))) bb at
      open Six S (cata-lin-I₁ n1 l1) C (cata-lin-I₂ n1 l1) (cata-lin-I₃ l1) B public using (B⊆; I₁⊆; I₂⊆; I₃⊆; closes-six)
      closes : ∀ {D} → Defd D (cata-trace-of (cata-dispatch strat-linear bb n1 l1 at)) → Closes D at
             → Closes D (cata-trace-of (cata-dispatch strat-linear bb n1 l1 at))
      closes d cat = closes-six
        (inj₁ (thk∈ (ℓ o (suc (suc (suc (suc l1))))) d (B⊆ (there (here refl)))) ∷ [])
        (inj₁ (lab∈ (ℓ o (suc l1)) d (I₁⊆ (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (here refl))))))))))))))))))))))))))) ∷
         inj₁ (lab∈ (ℓ o l1) d (I₁⊆ (there (there (there (here refl)))))) ∷ [])
        []
        (inj₁ (lab∈ (ℓ o (suc (suc (suc l1)))) d (I₃⊆ (there (there (here refl))))) ∷ [])
        (inj₁ (lab∈ (ℓ o (suc (suc l1))) d (I₂⊆ (here refl))) ∷ [])
        (body-closes _ _ bb at (defd-⊆ B⊆ d) cat)


  ------------------------------------------------------------------------
  -- THE COMPILE-TIME FUNCTOR WALKS. A `⊕` level owns `lb` and `suc lb`: it
  -- branches to `lb` and jumps to `suc lb`, and defines both itself.
  ------------------------------------------------------------------------
  visit-closes : ∀ (todo tv tb : ℕ) (F : Functor) (s lb : ℕ) {D}
               → Defd D (visit-walk todo tv tb F s lb) → Closes D (visit-walk todo tv tb F s lb)
  visit-closes todo tv tb (K _)   s lb d = []
  visit-closes todo tv tb Id      s lb d = []
  visit-closes todo tv tb (F ⊕ G) s lb d =
    inj₁ (lab∈ (ℓ o lb) d (there (there (there (∈-++⁺ʳ VG (there (here refl))))))) ∷
    closes-++ VG (Bc ++ (VF ++ Cc)) (visit-closes todo tv tb G (s + 4) (suc (suc lb) + lsize F) (defd-⊆ VG⊆ d))
      (inj₁ (lab∈ (ℓ o (suc lb)) d (there (there (there (∈-++⁺ʳ VG (there (there (there (there (∈-++⁺ʳ VF (here refl))))))))))) ∷
       closes-++ VF Cc (visit-closes todo tv tb F (s + 4) (suc (suc lb)) (defd-⊆ VF⊆ d)) [])
    where
      VG = visit-walk todo tv tb G (s + 4) (suc (suc lb) + lsize F)
      VF = visit-walk todo tv tb F (s + 4) (suc (suc lb))
      Bc = instr-ctrl (c-jmp (ℓ o (suc lb))) ∷ instr-ctrl (c-label (ℓ o lb)) ∷ load-indirect-suc ∷ mov-to-input ∷ []
      Cc = instr-ctrl (c-label (ℓ o (suc lb))) ∷ []
      VG⊆ : VG ⊆ visit-walk todo tv tb (F ⊕ G) s lb
      VG⊆ m = there (there (there (∈-++⁺ˡ m)))
      VF⊆ : VF ⊆ visit-walk todo tv tb (F ⊕ G) s lb
      VF⊆ m = there (there (there (∈-++⁺ʳ VG (there (there (there (there (∈-++⁺ˡ m))))))))
  visit-closes todo tv tb (F ⊗ G) s lb d =
    closes-++ VF (Bc ++ VG) (visit-closes todo tv tb F (s + 4) lb (defd-⊆ VF⊆ d))
      (visit-closes todo tv tb G (s + 4) (lb + lsize F) (defd-⊆ VG⊆ d))
    where
      VF = visit-walk todo tv tb F (s + 4) lb
      VG = visit-walk todo tv tb G (s + 4) (lb + lsize F)
      Bc = restore-input s ∷ load-indirect-suc ∷ mov-to-input ∷ []
      VF⊆ : VF ⊆ visit-walk todo tv tb (F ⊗ G) s lb
      VF⊆ m = there (there (there (there (∈-++⁺ˡ m))))
      VG⊆ : VG ⊆ visit-walk todo tv tb (F ⊗ G) s lb
      VG⊆ m = there (there (there (there (∈-++⁺ʳ VF (there (there (there (m))))))))

  rebuild-closes : ∀ (val tv tb : ℕ) (F : Functor) (s lb : ℕ) {D}
                 → Defd D (rebuild-walk val tv tb F s lb) → Closes D (rebuild-walk val tv tb F s lb)
  rebuild-closes val tv tb (K _)   s lb d = []
  rebuild-closes val tv tb Id      s lb d = []
  rebuild-closes val tv tb (F ⊕ G) s lb d =
    inj₁ (lab∈ (ℓ o lb) d (there (there (there (∈-++⁺ʳ RG (there (there (there (there (there (there (there (there (there (there (here refl)))))))))))))))) ∷
    closes-++ RG (wrap-sum 1 s ++ (Bc ++ (RF ++ (wrap-sum 0 s ++ Cc))))
      (rebuild-closes val tv tb G (s + 4) (suc (suc lb) + lsize F) (defd-⊆ RG⊆ d))
      (inj₁ (lab∈ (ℓ o (suc lb)) d (there (there (there (∈-++⁺ʳ RG (there (there (there (there (there (there (there (there (there (there (there (there (there (∈-++⁺ʳ RF (there (there (there (there (there (there (there (there (there (here refl))))))))))))))))))))))))))))) ∷
       closes-++ RF (wrap-sum 0 s ++ Cc) (rebuild-closes val tv tb F (s + 4) (suc (suc lb)) (defd-⊆ RF⊆ d)) [])
    where
      RG = rebuild-walk val tv tb G (s + 4) (suc (suc lb) + lsize F)
      RF = rebuild-walk val tv tb F (s + 4) (suc (suc lb))
      Bc = instr-ctrl (c-jmp (ℓ o (suc lb))) ∷ instr-ctrl (c-label (ℓ o lb)) ∷ load-indirect-suc ∷ mov-to-input ∷ []
      Cc = instr-ctrl (c-label (ℓ o (suc lb))) ∷ []
      RG⊆ : RG ⊆ rebuild-walk val tv tb (F ⊕ G) s lb
      RG⊆ m = there (there (there (∈-++⁺ˡ m)))
      RF⊆ : RF ⊆ rebuild-walk val tv tb (F ⊕ G) s lb
      RF⊆ m = there (there (there (∈-++⁺ʳ RG (there (there (there (there (there (there (there (there (there (there (there (there (there (∈-++⁺ˡ m)))))))))))))))))
  rebuild-closes val tv tb (F ⊗ G) s lb d =
    closes-++ RG (Bc ++ (RF ++ Dc)) (rebuild-closes val tv tb G (s + 4) (lb + lsize F) (defd-⊆ RG⊆ d))
      (closes-++ RF Dc (rebuild-closes val tv tb F (s + 4) lb (defd-⊆ RF⊆ d)) [])
    where
      RG = rebuild-walk val tv tb G (s + 4) (lb + lsize F)
      RF = rebuild-walk val tv tb F (s + 4) lb
      Bc = store-at-slot (s + 2) ∷ restore-input s ∷ load-indirect ∷ mov-to-input ∷ []
      Dc = store-at-slot (suc s) ∷ instr-alloc-heap 2 ∷ store-at-slot (s + 3) ∷ mov-to-input ∷
           load-from-slot (suc s) ∷ store-indirect ∷ load-from-slot (s + 2) ∷ store-indirect-suc ∷
           load-from-slot (s + 3) ∷ []
      RG⊆ : RG ⊆ rebuild-walk val tv tb (F ⊗ G) s lb
      RG⊆ m = there (there (there (there (∈-++⁺ˡ m))))
      RF⊆ : RF ⊆ rebuild-walk val tv tb (F ⊗ G) s lb
      RF⊆ m = there (there (there (there (∈-++⁺ʳ RG (there (there (there (there (∈-++⁺ˡ m)))))))))

  ------------------------------------------------------------------------
  -- THE RE-SUSPENSION PASS (D199): its code addresses name the `Ana` block
  -- (`lbl`, which the caller has defined); its `⊕` levels are `case`'s.
  ------------------------------------------------------------------------
  resusp-closes : ∀ (n l : ℕ) (lbl : LabelId) (env : ℕ) {F} (wf : WellFormedFI F) {D}
                → thunkSym lbl ∈ D
                → Defd D (proj₂ (proj₂ (resuspend-layer n l lbl env wf)))
                → Closes D (proj₂ (proj₂ (resuspend-layer n l lbl env wf)))
  resusp-closes n l lbl env (wf-K _) h d = []
  resusp-closes n l lbl env wf-Id    h d = inj₁ h ∷ []
  resusp-closes n l lbl env (wf-Prod wfF wfG) h d =
    closes-++ tF _ (resusp-closes (suc (suc (suc n))) l lbl env wfF h (defd-⊆ tF⊆ d))
      (closes-++ tG _ (resusp-closes (proj₁ RF) (proj₁ (proj₂ RF)) lbl env wfG h (defd-⊆ tG⊆ d)) [])
    where
      RF = resuspend-layer (suc (suc (suc n))) l lbl env wfF
      tF = proj₂ (proj₂ RF)
      tG = proj₂ (proj₂ (resuspend-layer (proj₁ RF) (proj₁ (proj₂ RF)) lbl env wfG))
      W = proj₂ (proj₂ (resuspend-layer n l lbl env (wf-Prod wfF wfG)))
      tF⊆ : tF ⊆ W
      tF⊆ m = there (there (there (∈-++⁺ˡ m)))
      tG⊆ : tG ⊆ W
      tG⊆ m = there (there (there (∈-++⁺ʳ tF (there (there (there (there (there (there (there (there (∈-++⁺ˡ m))))))))))))
  resusp-closes n l lbl env (wf-Sum wfF wfG) h d =
    inj₁ (lab∈ (ℓ o l) d inl∈) ∷
    closes-++ (tG ++ ch 1) _ (closes-++ tG (ch 1) (resusp-closes (proj₁ RF) (proj₁ (proj₂ RF)) lbl env wfG h (defd-⊆ tG⊆ d)) [])
      (inj₁ (lab∈ (ℓ o (suc l)) d end∈) ∷
       closes-++ (tF ++ ch 0) _ (closes-++ tF (ch 0) (resusp-closes (suc (suc (suc n))) (suc (suc l)) lbl env wfF h (defd-⊆ tF⊆ d)) []) [])
    where
      RF = resuspend-layer (suc (suc (suc n))) (suc (suc l)) lbl env wfF
      tF = proj₂ (proj₂ RF)
      tG = proj₂ (proj₂ (resuspend-layer (proj₁ RF) (proj₁ (proj₂ RF)) lbl env wfG))
      ch : ℕ → AbstractTrace
      ch tag = store-at-slot (suc (suc n)) ∷ instr-alloc-heap 2 ∷ store-at-slot (suc n) ∷ mov-to-input ∷
               load-from-slot (suc (suc n)) ∷ store-indirect-suc ∷ instr-load-tag-lit tag ∷ store-indirect ∷
               load-from-slot (suc n) ∷ []
      W = proj₂ (proj₂ (resuspend-layer n l lbl env (wf-Sum wfF wfG)))
      tG⊆ : tG ⊆ W
      tG⊆ m = there (there (there (there (there (∈-++⁺ˡ (∈-++⁺ˡ m))))))
      inl∈ : instr-ctrl (c-label (ℓ o l)) ∈ W
      inl∈ = there (there (there (there (there (∈-++⁺ʳ (tG ++ ch 1) (there (here refl)))))))
      tF⊆ : tF ⊆ W
      tF⊆ m = there (there (there (there (there (∈-++⁺ʳ (tG ++ ch 1) (there (there (there (there (∈-++⁺ˡ (∈-++⁺ˡ m)))))))))))
      end∈ : instr-ctrl (c-label (ℓ o (suc l))) ∈ W
      end∈ = there (there (there (there (there (∈-++⁺ʳ (tG ++ ch 1) (there (there (there (there (∈-++⁺ʳ (tF ++ ch 0) (here refl)))))))))))

  module BrS where
    module _ (F : Functor) (bb n1 l1 : ℕ) (at : AbstractTrace) where
      Lb = l1 + 4 + lsize F + lsize F
      B0 = n1 + 7 + (4 * fsize F) + 4
      S = cata-call-setup B0 (B0 + 1) (B0 + 2) (B0 + 3) Lb
      C = cata-call B0 (B0 + 1) (B0 + 3)
      B = cata-body Lb (Lb + 1) bb at
      I₁ = cata-br-I₁ F n1 l1
      I₂ = cata-br-I₂ n1 l1
      R₂ = I₂ ++ B
      R₁ = C ++ R₂
      R₀ = I₁ ++ R₁
      T  = S ++ R₀
      I₁⊆ : I₁ ⊆ T
      I₁⊆ = ⊆-trans (⊆-++ˡ I₁ R₁) (⊆-++ʳ S R₀)
      R₂⊆ : R₂ ⊆ T
      R₂⊆ = ⊆-trans (⊆-++ʳ C R₂) (⊆-trans (⊆-++ʳ I₁ R₁) (⊆-++ʳ S R₀))
      I₂⊆ : I₂ ⊆ T
      I₂⊆ = ⊆-trans (⊆-++ˡ I₂ B) R₂⊆
      B⊆ : B ⊆ T
      B⊆ = ⊆-trans (⊆-++ʳ I₂ B) R₂⊆
      VW = visit-walk n1 (n1 + 4) (n1 + 5) F (n1 + 7) (l1 + 4)
      RW = rebuild-walk (n1 + 2) (n1 + 4) (n1 + 5) F (n1 + 7) (l1 + 4 + lsize F)
      VW⊆ : VW ⊆ I₁
      VW⊆ m = there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (∈-++⁺ˡ m))))))))))))))))))))))))))))))))))))))))))))))
      RW⊆ : RW ⊆ I₁
      RW⊆ m = there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (∈-++⁺ʳ VW (there (there (there (there (there (there (there (there (there (there (∈-++⁺ˡ m)))))))))))))))))))))))))))))))))))))))))))))))))))))))))
      closes : ∀ {D} → Defd D (cata-trace-of (cata-dispatch (strat-branching F) bb n1 l1 at)) → Closes D at
             → Closes D (cata-trace-of (cata-dispatch (strat-branching F) bb n1 l1 at))
      closes d cat =
        closes-++ S R₀ (inj₁ (thk∈ (ℓ o Lb) d (B⊆ (there (here refl)))) ∷ [])
          (closes-++ I₁ R₁
            (inj₁ (lab∈ (ℓ o (suc l1)) d (I₁⊆ (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (∈-++⁺ʳ VW (there (here refl))))))))))))))))))))))))))))))))))))))))))))))))))) ∷
             closes-++ VW _ (visit-closes n1 (n1 + 4) (n1 + 5) F (n1 + 7) (l1 + 4) (defd-⊆ (⊆-trans VW⊆ I₁⊆) d))
               (inj₁ (lab∈ (ℓ o l1) d (I₁⊆ (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (here refl))))))))))))))))))))))))))) ∷
                inj₁ (lab∈ (ℓ o (l1 + 3)) d (I₂⊆ (there (there (there (there (there (there (there (there (there (there (there (here refl)))))))))))))) ∷
                closes-++ RW _ (rebuild-closes (n1 + 2) (n1 + 4) (n1 + 5) F (n1 + 7) (l1 + 4 + lsize F)
                                  (defd-⊆ (⊆-trans RW⊆ I₁⊆) d)) []))
            (closes-++ C R₂ []
              (closes-++ I₂ B (inj₁ (lab∈ (ℓ o (l1 + 2)) d (I₁⊆ (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (∈-++⁺ʳ VW (there (there (here refl)))))))))))))))))))))))))))))))))))))))))))))))))))) ∷ [])
                (body-closes Lb (Lb + 1) bb at (defd-⊆ B⊆ d) cat))))

  at⊆ : ∀ (st : CataStrategy) (bb n1 l1 : ℕ) (at : AbstractTrace)
      → at ⊆ cata-trace-of (cata-dispatch st bb n1 l1 at)
  cata-closes : ∀ (st : CataStrategy) (bb n1 l1 : ℕ) (at : AbstractTrace) {D}
              → Defd D (cata-trace-of (cata-dispatch st bb n1 l1 at)) → Closes D at
              → Closes D (cata-trace-of (cata-dispatch st bb n1 l1 at))

  at⊆ strat-const bb n1 l1 at =
    ⊆-trans (at⊆body l1 (l1 + 1) bb at)
      (⊆-trans (⊆-++ʳ (cata-call n1 (n1 + 1) (n1 + 3)) (cata-body l1 (l1 + 1) bb at))
               (⊆-++ʳ (cata-call-setup n1 (n1 + 1) (n1 + 2) (n1 + 3) l1) _))
  at⊆ strat-nat bb n1 l1 at = ⊆-trans (at⊆body _ _ bb at) (NatS.B⊆ bb n1 l1 at)
  at⊆ strat-linear bb n1 l1 at = ⊆-trans (at⊆body _ _ bb at) (LinS.B⊆ bb n1 l1 at)
  at⊆ (strat-branching F) bb n1 l1 at = ⊆-trans (at⊆body _ _ bb at) (BrS.B⊆ F bb n1 l1 at)

  cata-closes strat-const bb n1 l1 at {D} d cat =
    closes-++ S (C ++ B) (setup-closes n1 (n1 + 1) (n1 + 2) (n1 + 3) l1 (thk∈ (ℓ o l1) d (B⊆T (there (here refl)))))
      (closes-++ C B [] (body-closes l1 (l1 + 1) bb at (defd-⊆ B⊆T d) cat))
    where
      S = cata-call-setup n1 (n1 + 1) (n1 + 2) (n1 + 3) l1
      C = cata-call n1 (n1 + 1) (n1 + 3)
      B = cata-body l1 (l1 + 1) bb at
      B⊆T : B ⊆ S ++ (C ++ B)
      B⊆T = ⊆-trans (⊆-++ʳ C B) (⊆-++ʳ S (C ++ B))
  cata-closes strat-nat bb n1 l1 at {D} d cat = NatS.closes bb n1 l1 at d cat
  cata-closes strat-linear bb n1 l1 at {D} d cat = LinS.closes bb n1 l1 at d cat
  cata-closes (strat-branching F) bb n1 l1 at {D} d cat = BrS.closes F bb n1 l1 at d cat


  ------------------------------------------------------------------------
  -- THE INDUCTION.
  ------------------------------------------------------------------------

  Unit : ℕ × ℕ × AbstractTrace × List (LabelId × ℕ × AbstractTrace) → AbstractTrace
  Unit X = trace-of X ++ blocks-layout (bodies-of X)

  sigop-closes : ∀ {A B D} (si : SigOpInfo A B) (n : ℕ) (m : Maybe CmpOp)
               → All G (sigop-syms si m) → Closes D (sigop-code si n m)
  sigop-closes si n nothing  (g ∷ []) = inj₂ g ∷ []
  sigop-closes si n (just c) (g ∷ []) = inj₂ g ∷ []

  close : ∀ {A B} (ir : IR A B) (n l : ℕ) {D}
        → Defd D (Unit (ir-to-trace' n l ir)) → NOK ir
        → Closes D (trace-of (ir-to-trace' n l ir)) × Closes D (blocks-layout (bodies-of (ir-to-trace' n l ir)))
  close id       n l d ok = [] , []
  close fst      n l d ok = [] , []
  close snd      n l d ok = [] , []
  close terminal n l d ok = [] , []
  close initial  n l d ok = [] , []
  close inl      n l d ok = [] , []
  close inr      n l d ok = [] , []
  close apply    n l d ok = [] , []
  close (In _)    n l d ok = [] , []
  close (out-μ _) n l d ok = [] , []
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
  close ⟨ f , g ⟩ n l {D} d (okf , okg) =
    closes-++ ft R₁ (proj₁ cf) (closes-++ gt R₂ (proj₁ cg) [])
    , subst (Closes D) (sym (blocks-layout-++ fb gb))
            (closes-++ (blocks-layout fb) (blocks-layout gb) (proj₂ cf) (proj₂ cg))
    where
      X = ir-to-trace' (suc (suc (suc (suc n)))) l f
      ft = trace-of X ; fb = bodies-of X
      Y = ir-to-trace' (proj₁ X) (proj₁ (proj₂ X)) g
      gt = trace-of Y ; gb = bodies-of Y
      R₂ = store-at-slot (suc (suc n)) ∷ instr-alloc-heap 2 ∷ store-at-slot (suc (suc (suc n))) ∷
           mov-to-input ∷ load-from-slot (suc n) ∷ store-indirect ∷ load-from-slot (suc (suc n)) ∷
           store-indirect-suc ∷ load-from-slot (suc (suc (suc n))) ∷ []
      R₁ = store-at-slot (suc n) ∷ restore-input n ∷ (gt ++ R₂)
      T = mov-to-output ∷ store-at-slot n ∷ (ft ++ R₁)
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
  close (case f g) n l {D} d (okf , okg) =
    inj₁ (lab∈ (ℓ o l) d inl∈) ∷
      closes-++ gt R₁ (proj₁ cg) (inj₁ (lab∈ (ℓ o (suc l)) d end∈) ∷ closes-++ ft R₂ (proj₁ cf) [])
    , subst (Closes D) (sym (blocks-layout-++ fb gb))
            (closes-++ (blocks-layout fb) (blocks-layout gb) (proj₂ cf) (proj₂ cg))
    where
      X = ir-to-trace' n (suc (suc l)) f
      ft = trace-of X ; fb = bodies-of X
      Y = ir-to-trace' (proj₁ X) (proj₁ (proj₂ X)) g
      gt = trace-of Y ; gb = bodies-of Y
      R₂ = instr-ctrl (c-label (ℓ o (suc l))) ∷ []
      R₁ = instr-ctrl (c-jmp (ℓ o (suc l))) ∷ instr-ctrl (c-label (ℓ o l)) ∷
           load-indirect-suc ∷ mov-to-input ∷ (ft ++ R₂)
      T = instr-ctrl (c-branch-tag-zero (ℓ o l)) ∷ load-indirect-suc ∷ mov-to-input ∷ (gt ++ R₁)
      L = blocks-layout (fb ++ gb)
      inT : T ⊆ T ++ L
      inT = ⊆-++ˡ T L
      inL : blocks-layout fb ++ blocks-layout gb ⊆ T ++ L
      inL = ⊆-trans (layout-++⁻ fb gb) (⊆-++ʳ T L)
      R₁T : R₁ ⊆ T
      R₁T m = there (there (there (∈-++⁺ʳ gt m)))
      inl∈ : instr-ctrl (c-label (ℓ o l)) ∈ T ++ L
      inl∈ = inT (R₁T (there (here refl)))
      end∈ : instr-ctrl (c-label (ℓ o (suc l))) ∈ T ++ L
      end∈ = inT (R₁T (there (there (there (there (∈-++⁺ʳ ft (here refl)))))))
      ftT : ft ⊆ T
      ftT m = R₁T (there (there (there (there (∈-++⁺ˡ m)))))
      gtT : gt ⊆ T
      gtT m = there (there (there (∈-++⁺ˡ m)))
      cf = close f n (suc (suc l))
                 (defd-⊆ (++-⊆ ft (blocks-layout fb) (⊆-trans ftT inT)
                            (⊆-trans (⊆-++ˡ (blocks-layout fb) (blocks-layout gb)) inL)) d) okf
      cg = close g (proj₁ X) (proj₁ (proj₂ X))
                 (defd-⊆ (++-⊆ gt (blocks-layout gb) (⊆-trans gtT inT)
                            (⊆-trans (⊆-++ʳ (blocks-layout fb) (blocks-layout gb)) inL)) d) okg
  close (curry b) n l {D} d okb =
    inj₁ (thk∈ (ℓ o l) d thk∈U) ∷ []
    , closes-++ (block-layout (ℓ o l , bb , bt)) (blocks-layout bbs)
                (closes-++ bt (instr-ctrl (c-ret bb) ∷ []) (proj₁ cb) [])
                (proj₂ cb)
    where
      X = ir-to-trace' 0 (suc (suc l)) b
      bb = proj₁ X ; bt = trace-of X ; bbs = bodies-of X
      T = trace-of (ir-to-trace' n l (curry b))
      L = blocks-layout ((ℓ o l , bb , bt) ∷ bbs)
      thk∈U : instr-ctrl (c-thunk (ℓ o l) bb) ∈ T ++ L
      thk∈U = ∈-++⁺ʳ T (here refl)
      btU : bt ⊆ T ++ L
      btU m = ∈-++⁺ʳ T (there (∈-++⁺ˡ {ys = blocks-layout bbs} (∈-++⁺ˡ m)))
      bbsU : blocks-layout bbs ⊆ T ++ L
      bbsU m = ∈-++⁺ʳ T (∈-++⁺ʳ (block-layout (ℓ o l , bb , bt)) m)
      cb = close b 0 (suc (suc l)) (defd-⊆ (++-⊆ bt (blocks-layout bbs) btU bbsU) d) okb
  close (in-ν w) n l {D} d ok =
    inj₁ (thk∈ (ℓ o l) d (∈-++⁺ʳ (trace-of (ir-to-trace' n l (in-ν w))) (here refl))) ∷ [] , []
  close (Cata {F} w alg) n l {D} d ok =
    cata-closes (cata-strategy ⌈ F ⌉F) bb n l1 at (defd-⊆ (⊆-++ˡ T L) d) (proj₁ ca)
    , proj₂ ca
    where
      X = ir-to-trace' 0 l alg
      bb = proj₁ X ; l1 = proj₁ (proj₂ X) ; at = trace-of X ; ab = bodies-of X
      T = cata-trace-of (cata-dispatch (cata-strategy ⌈ F ⌉F) bb n l1 at)
      L = blocks-layout ab
      ca = close alg 0 l (defd-⊆ (++-⊆ at L (⊆-trans (at⊆ (cata-strategy ⌈ F ⌉F) bb n l1 at) (⊆-++ˡ T L))
                                           (⊆-++ʳ T L)) d) ok
  close (Ana wf c) n l {D} d ok =
    inj₁ (thk∈ (ℓ o l) d (∈-++⁺ʳ T (here refl))) ∷ []
    , closes-++ (block-layout (ℓ o l , bb , bt)) (blocks-layout cbs)
                (closes-++ bt (instr-ctrl (c-ret bb) ∷ [])
                   (closes-++ ct rt (proj₁ cc)
                      (resusp-closes cb l2 (ℓ o l) 0 wf (thk∈ (ℓ o l) d (∈-++⁺ʳ T (here refl)))
                                     (defd-⊆ rtU d)))
                   [])
                (proj₂ cc)
    where
      X = ir-to-trace' 1 (suc l) c
      cb = proj₁ X ; l2 = proj₁ (proj₂ X) ; ct = trace-of X ; cbs = bodies-of X
      R = resuspend-layer cb l2 (ℓ o l) 0 wf
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

