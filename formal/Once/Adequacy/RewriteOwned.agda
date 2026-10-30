-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.RewriteOwned — plan 0.129 B5: AFTER THE ARITH PASS, EVERY
-- SIGOP THE COMPILER OWNS NAMES A BLOCK THE PASS RETURNED.
--
-- The emitter lowers every SigOp to a call of its symbol. An interpretation's
-- SigOp is resolved by `ld`; a compiler-owned one (`Internal`: a primitive or
-- an arith block) only by a block in the file. So the pass leaves no bare
-- primitive: each is a block, or a comparison, whose lowering calls its own
-- block (`cmp-trace`), which the pass registers (`sigop-blocks`); and a block
-- it meets is rebuilt as its canonical `block-info` and registered
-- (`bare-sigop`). Before B5 a float operation over a `Float` input stayed bare
-- (`shape-of` had no `Float` case) and failed to link, while
-- `arith-sigop-contract` assumed it could not.
------------------------------------------------------------------------

module Once.Adequacy.RewriteOwned where

open import Data.Bool using (true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Data.List.Relation.Unary.All using (All; []; _∷_) renaming (map to All-map)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)

open import Once.Spec.Name using (bare)
open import Once.Spec.Type using (Type; Base; ∅ₖ)
open import Once.IR
import Once.IRTy as II
open import Once.SigOp.Info using (SigOpInfo; mk-info'; SigOpSem; Internal;
                                   blockV; primV; ffiV; callsV; emitsV; haltsV; module SigOpInfo)
open SigOpInfo using (name; sem; baseA; conB)
open import Once.Arith.Prim using (ArithPrim; p-add; p-sub; p-mul; p-div; p-mod; p-neg;
                                   p-fadd; p-fsub; p-fmul; p-fdiv; p-i2f; p-cmp)
open import Once.Arith.CmpOp using (CmpOp)
open import Once.Arith.SigOp.Compare using (cmp-of; cmp-block; cmp-block-info)
open import Once.Arith.SigOp.Block using (block-info; block-name)
open import Once.Arith.Machine.IR using (ArithBlock; mk-block; module ArithBlock; shape-as-type; MArithIR)
open import Once.Arith.Type using (NInt; NFloat)
open ArithBlock using (block-body)
open import Once.Arith.Machine.Rewrite using (rewrite-ir; walk-both; prefix-at; try-lift; bare-at; bare-sigop; shape-of; has-op; block-as-ir; sigop-blocks)
open import Once.Arith.Machine.Recognise using (recognise-body; recognise-body-float)
open import Once.CCC.Codegen.NodesOK using (SigLeaves)
open import Once.CCC.Codegen.CallOK using (Calls)
open import Once.Denotation.Program using (leaves-map; IRFun; IRProgram; module IRProgram; module IRFun)
open IRProgram using (main; table)
open IRFun using (fbody)
open import Once.Compile using (rewrite-program; rewrite-table; program-blocks; table-blocks)

------------------------------------------------------------------------
-- A primitive that is not a comparison LIFTS: `SigOp si ∘ id` is one
-- operation over its own input, a block.
------------------------------------------------------------------------

private
  lifts-at : ∀ {X Y} (nm : _) (p : ArithPrim X Y) (bA : Base ∅ₖ X) (cB : Base ∅ₖ Y)
           → cmp-of (primV p) ≡ nothing
           → try-lift (SigOp (mk-info' nm (primV p) bA cB) ∘ id) ≡ nothing → ⊥
  lifts-at nm p-add  bA cB _ ()
  lifts-at nm p-sub  bA cB _ ()
  lifts-at nm p-mul  bA cB _ ()
  lifts-at nm p-div  bA cB _ ()
  lifts-at nm p-mod  bA cB _ ()
  lifts-at nm p-neg  bA cB _ ()
  lifts-at nm p-fadd bA cB _ ()
  lifts-at nm p-fsub bA cB _ ()
  lifts-at nm p-fmul bA cB _ ()
  lifts-at nm p-fdiv bA cB _ ()
  lifts-at nm p-i2f  bA cB _ ()
  lifts-at nm (p-cmp o) bA cB () _

------------------------------------------------------------------------
-- What the pass guarantees.
------------------------------------------------------------------------

-- A compiler-owned SigOp names one of `bs`.
Named : List ArithBlock → ∀ {X Y} → SigOpInfo X Y → Set
Named bs si = Internal (sem si) → Σ ArithBlock (λ b → b ∈ bs × name si ≡ bare (block-name (block-body b)))

Owned : List ArithBlock → ∀ {A B} → IR A B → Set
Owned bs = SigLeaves (λ si → Calls (Named bs) si (cmp-of (sem si)))

------------------------------------------------------------------------
-- More blocks name as much.
------------------------------------------------------------------------

private
  Sub : List ArithBlock → List ArithBlock → Set
  Sub bs cs = ∀ {b} → b ∈ bs → b ∈ cs

  calls-⊆ : ∀ {bs cs} → Sub bs cs → ∀ {X Y} (si : SigOpInfo X Y) (m : Maybe CmpOp)
          → Calls (Named bs) si m → Calls (Named cs) si m
  calls-⊆ s si nothing  c int = let (b , m , e) = c int in b , s m , e
  calls-⊆ s si (just o) c int = let (b , m , e) = c int in b , s m , e

owned-⊆ : ∀ {bs cs} → (∀ {b} → b ∈ bs → b ∈ cs) → ∀ {A B} (ir : IR A B) → Owned bs ir → Owned cs ir
owned-⊆ s = leaves-map (λ _ _ _ c → c) (λ si → calls-⊆ s si (cmp-of (sem si)))

owned-++ˡ : ∀ bs cs {A B} (ir : IR A B) → Owned bs ir → Owned (bs ++ cs) ir
owned-++ˡ bs cs = owned-⊆ (∈-++⁺ˡ {xs = bs} {ys = cs})

owned-++ʳ : ∀ bs cs {A B} (ir : IR A B) → Owned cs ir → Owned (bs ++ cs) ir
owned-++ʳ bs cs = owned-⊆ (∈-++⁺ʳ bs)

------------------------------------------------------------------------
-- A lifted subtree is one block SigOp, naming the block it returns.
------------------------------------------------------------------------

private
  JustOwned : ∀ {A B} → Maybe (IR A B × ArithBlock) → Set
  JustOwned nothing          = ⊤
  JustOwned (just (ir′ , b)) = Owned (b ∷ []) ir′

  block-owned : ∀ {A sh n} (eq : A ≡ II.⌊ shape-as-type sh ⌋) (body : MArithIR sh n)
              → Owned (mk-block sh n body ∷ []) (block-as-ir eq body)
  block-owned {n = NInt}   refl body _ = _ , here refl , refl
  block-owned {n = NFloat} refl body _ = _ , here refl , refl

  try-lift-owned : ∀ {A B} (ir : IR A B) → JustOwned (try-lift ir)
  try-lift-owned {A} {II.Int} ir with shape-of A
  ... | nothing = tt
  ... | just (sh , eq) with recognise-body sh ir
  ...   | nothing = tt
  ...   | just body with has-op body
  ...     | false = tt
  ...     | true  = block-owned eq body
  try-lift-owned {A} {II.Float} ir with shape-of A
  ... | nothing = tt
  ... | just (sh , eq) with recognise-body-float sh ir
  ...   | nothing = tt
  ...   | just body with has-op body
  ...     | false = tt
  ...     | true  = block-owned eq body
  try-lift-owned {A} {II.Unit}     ir = tt
  try-lift-owned {A} {II.Void}     ir = tt
  try-lift-owned {A} {_ II.* _}    ir = tt
  try-lift-owned {A} {_ II.+ _}    ir = tt
  try-lift-owned {A} {_ II.⇛ _}    ir = tt
  try-lift-owned {A} {II.μ-type _} ir = tt
  try-lift-owned {A} {II.ν-type _} ir = tt

------------------------------------------------------------------------
-- A SigOp the pass leaves bare is a comparison (its block registered), a
-- block (rebuilt and registered), or the interpretation's: a primitive lifts.
------------------------------------------------------------------------

private
  prim-stays : ∀ {X Y} nm (p : ArithPrim X Y) bA cB → try-lift (SigOp (mk-info' nm (primV p) bA cB) ∘ id) ≡ nothing
             → (m : Maybe CmpOp) → cmp-of (primV p) ≡ m → Calls (Named (sigop-blocks m)) (mk-info' nm (primV p) bA cB) m
  prim-stays nm p bA cB tl (just o) _ _   = cmp-block o , here refl , refl
  prim-stays nm p bA cB tl nothing  c int = ⊥-elim (lifts-at nm p bA cB c tl)

  stays : ∀ {X Y} nm (s : SigOpSem X Y) bA cB → try-lift (SigOp (mk-info' nm s bA cB) ∘ id) ≡ nothing
        → Owned (proj₂ (bare-sigop nm s bA cB)) (proj₁ (bare-sigop nm s bA cB))
  stays nm (blockV {sh} {n} e refl refl) bA cB tl _ = mk-block sh n e , here refl , refl
  stays nm (primV p)  bA cB tl = prim-stays nm p bA cB tl (cmp-of (primV p)) refl
  stays nm ffiV       bA cB tl ()
  stays nm callsV     bA cB tl ()
  stays nm (emitsV _) bA cB tl ()
  stays nm (haltsV _) bA cB tl ()

  bare-owned : ∀ {X Y} (si : SigOpInfo X Y)
             → ∀ (d : Maybe (IR II.⌊ X ⌋ II.⌊ Y ⌋ × ArithBlock)) → try-lift (SigOp si ∘ id) ≡ d → JustOwned d
             → Owned (proj₂ (bare-at si d)) (proj₁ (bare-at si d))
  bare-owned si (just _) _  jo = jo
  bare-owned si nothing  tl _  = stays (name si) (sem si) (baseA si) (conB si) tl

------------------------------------------------------------------------
-- THE PASS NAMES EVERY COMPILER-OWNED SIGOP'S BLOCK.
------------------------------------------------------------------------

private
  -- (a chain's head lifted as a block, plan 0.129 B4)
  prefix-owned : ∀ {A X B C} (g : IR B C) (f₁ : IR X B) (f₂ : IR A X) (f : IR A B) → f ≡ f₁ ∘ f₂
               → ∀ (d : Maybe (IR X C × ArithBlock)) → JustOwned d
               → Owned (proj₂ (prefix-at g f₁ f₂ f d)) (proj₁ (prefix-at g f₁ f₂ f d))
  both-owned : ∀ {A B C} (g : IR B C) (f : IR A B)
             → Owned (proj₂ (walk-both g f)) (proj₁ (walk-both g f))
  -- a pair's or a case's two sides
  two-owned : ∀ {A B C D} (f : IR A B) (g : IR C D)
            → Owned (proj₂ (rewrite-ir f) ++ proj₂ (rewrite-ir g)) (proj₁ (rewrite-ir f))
            × Owned (proj₂ (rewrite-ir f) ++ proj₂ (rewrite-ir g)) (proj₁ (rewrite-ir g))

rewrite-ir-owned : ∀ {A B} (ir : IR A B) → Owned (proj₂ (rewrite-ir ir)) (proj₁ (rewrite-ir ir))
rewrite-ir-owned ir with try-lift ir | try-lift-owned ir
... | just (ir′ , blk) | jo = jo
rewrite-ir-owned id           | nothing | _ = tt
rewrite-ir-owned (g ∘ f@(f₁ ∘ f₂)) | nothing | _ =
  prefix-owned g f₁ f₂ f refl (try-lift (g ∘ f₁)) (try-lift-owned (g ∘ f₁))
rewrite-ir-owned (g ∘ f@id) | nothing | _ = both-owned g f
rewrite-ir-owned (g ∘ f@(⟨ _ , _ ⟩)) | nothing | _ = both-owned g f
rewrite-ir-owned (g ∘ f@fst) | nothing | _ = both-owned g f
rewrite-ir-owned (g ∘ f@snd) | nothing | _ = both-owned g f
rewrite-ir-owned (g ∘ f@(inl {P} {Q})) | nothing | _ = both-owned g f
rewrite-ir-owned (g ∘ f@(inr {P} {Q})) | nothing | _ = both-owned g f
rewrite-ir-owned (g ∘ f@(case _ _)) | nothing | _ = both-owned g f
rewrite-ir-owned (g ∘ f@(terminal {P})) | nothing | _ = both-owned g f
rewrite-ir-owned (g ∘ f@initial) | nothing | _ = both-owned g f
rewrite-ir-owned (g ∘ f@(curry _)) | nothing | _ = both-owned g f
rewrite-ir-owned (g ∘ f@(apply {P} {Q})) | nothing | _ = both-owned g f
rewrite-ir-owned (g ∘ f@(In _)) | nothing | _ = both-owned g f
rewrite-ir-owned (g ∘ f@(out-μ _)) | nothing | _ = both-owned g f
rewrite-ir-owned (g ∘ f@(Cata _ _)) | nothing | _ = both-owned g f
rewrite-ir-owned (g ∘ f@(Out _)) | nothing | _ = both-owned g f
rewrite-ir-owned (g ∘ f@(in-ν _)) | nothing | _ = both-owned g f
rewrite-ir-owned (g ∘ f@(Ana _ _)) | nothing | _ = both-owned g f
rewrite-ir-owned (g ∘ f@(Iter _)) | nothing | _ = both-owned g f
rewrite-ir-owned (g ∘ f@(SigOp _)) | nothing | _ = both-owned g f
rewrite-ir-owned (g ∘ f@(Call _)) | nothing | _ = both-owned g f
rewrite-ir-owned (g ∘ f@(const _ _)) | nothing | _ = both-owned g f
rewrite-ir-owned fst          | nothing | _ = tt
rewrite-ir-owned snd          | nothing | _ = tt
rewrite-ir-owned ⟨ f , g ⟩    | nothing | _ = two-owned f g
rewrite-ir-owned inl          | nothing | _ = tt
rewrite-ir-owned inr          | nothing | _ = tt
rewrite-ir-owned (case f g)   | nothing | _ = two-owned f g
rewrite-ir-owned terminal     | nothing | _ = tt
rewrite-ir-owned initial      | nothing | _ = tt
rewrite-ir-owned (curry f)    | nothing | _ = rewrite-ir-owned f
rewrite-ir-owned apply        | nothing | _ = tt
rewrite-ir-owned (In w)       | nothing | _ = tt
rewrite-ir-owned (out-μ w)    | nothing | _ = tt
rewrite-ir-owned (Cata w f)   | nothing | _ = rewrite-ir-owned f
rewrite-ir-owned (Out w)      | nothing | _ = tt
rewrite-ir-owned (in-ν w)     | nothing | _ = tt
rewrite-ir-owned (Ana w f)    | nothing | _ = rewrite-ir-owned f
rewrite-ir-owned (Iter f)     | nothing | _ = rewrite-ir-owned f
rewrite-ir-owned (const p v)  | nothing | _ = tt
rewrite-ir-owned (SigOp si)   | nothing | _ = bare-owned si (try-lift (SigOp si ∘ id)) refl (try-lift-owned (SigOp si ∘ id))
rewrite-ir-owned (Call f)     | nothing | _ = tt

both-owned g f = two-owned g f

two-owned f g =
  owned-++ˡ (proj₂ (rewrite-ir f)) (proj₂ (rewrite-ir g)) (proj₁ (rewrite-ir f)) (rewrite-ir-owned f)
  , owned-++ʳ (proj₂ (rewrite-ir f)) (proj₂ (rewrite-ir g)) (proj₁ (rewrite-ir g)) (rewrite-ir-owned g)

prefix-owned g f₁ f₂ f e nothing _ = both-owned g f
prefix-owned g f₁ f₂ .(f₁ ∘ f₂) refl (just (ir′ , blk)) jo =
  owned-⊆ (λ { (here e) → here e }) ir′ jo
  , owned-++ʳ (blk ∷ []) (proj₂ (rewrite-ir f₂)) (proj₁ (rewrite-ir f₂)) (rewrite-ir-owned f₂)

------------------------------------------------------------------------
-- …over a program: `main` and every entry, against the program's blocks.
------------------------------------------------------------------------

private
  table-owned : ∀ (es : List IRFun) → All (λ e → Owned (table-blocks es) (fbody e)) (rewrite-table es)
  table-owned []       = []
  table-owned (e ∷ es) =
    owned-++ˡ (proj₂ (rewrite-ir (fbody e))) (table-blocks es) (proj₁ (rewrite-ir (fbody e))) (rewrite-ir-owned (fbody e))
    ∷ All-map (λ {x} o → owned-++ʳ (proj₂ (rewrite-ir (fbody e))) (table-blocks es) (fbody x) o) (table-owned es)

program-owned : ∀ (p : IRProgram)
              → Owned (program-blocks p) (main (rewrite-program p))
              × All (λ e → Owned (program-blocks p) (fbody e)) (table (rewrite-program p))
program-owned p =
  owned-++ˡ (proj₂ (rewrite-ir (main p))) (table-blocks (table p)) (proj₁ (rewrite-ir (main p))) (rewrite-ir-owned (main p))
  , All-map (λ {x} o → owned-++ʳ (proj₂ (rewrite-ir (main p))) (table-blocks (table p)) (fbody x) o)
            (table-owned (table p))
