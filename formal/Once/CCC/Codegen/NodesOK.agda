-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.NodesOK — plan 0.107 phase d: THE GLOBAL REFERENCES OF AN
-- IR, at its leaves.
--
-- `RefsClosed` closes every LOCAL reference an emitted fragment makes; what is
-- left is GLOBAL, and it is decided by the IR's leaves: a `Call f` names a
-- table entry's symbol, a `SigOp` names its block or an interpretation symbol
-- (`sigop-syms` — a comparison calls its block, D264). `NodesOK G ir` says
-- every such symbol satisfies `G`. Calls discharge it from linkedness
-- (`nodes-from`); SigOps from `SigLeaves`, a predicate on the SigOps alone.
------------------------------------------------------------------------

module Once.CCC.Codegen.NodesOK where

open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Relation.Unary.All.Properties using (++⁻)
open import Data.List.Relation.Unary.All using (All)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.String using (String)
open import Data.Unit using (⊤; tt)

open import Once.CanonicalName using (CanonicalName)
open import Once.CCC.Label using (callee; e-fn; labelSym)
open import Once.SigOp.Info using (SigOpInfo; sem; name)
open import Once.Target.Symbol using (once-symbol-path)
open import Once.Arith.CmpOp using (CmpOp)
open import Once.Arith.SigOp.Compare using (cmp-of; cmp-block-info)
open import Once.IR using (IR)
import Once.IR as IRm
open IRm.IR
open import Once.IRTy using (IRTy)
open import Once.Spec.Contract using (ISig)
open import Once.Denotation.Program using (IRFun; Linked; LinkedAt)

-- The symbol a SigOp's lowering calls: itself, or (a comparison) its block.
sigop-syms : ∀ {A B} → SigOpInfo A B → Maybe CmpOp → List String
sigop-syms si nothing  = once-symbol-path (name si) ∷ []
sigop-syms si (just c) = once-symbol-path (name (cmp-block-info c)) ∷ []

-- A predicate on an IR's SigOp leaves.
SigLeaves : (∀ {A B} → SigOpInfo A B → Set) → ∀ {A B} → IR A B → Set
SigLeaves P (g ∘ f)          = SigLeaves P g × SigLeaves P f
SigLeaves P ⟨ f , g ⟩        = SigLeaves P f × SigLeaves P g
SigLeaves P (case f g)       = SigLeaves P f × SigLeaves P g
SigLeaves P (curry f)        = SigLeaves P f
SigLeaves P (Cata _ alg)     = SigLeaves P alg
SigLeaves P (Ana _ coalg)    = SigLeaves P coalg
SigLeaves P (SigOp si)       = P si
SigLeaves P (Call _)         = ⊤
SigLeaves P id               = ⊤
SigLeaves P fst              = ⊤
SigLeaves P snd              = ⊤
SigLeaves P inl              = ⊤
SigLeaves P inr              = ⊤
SigLeaves P terminal         = ⊤
SigLeaves P initial          = ⊤
SigLeaves P apply            = ⊤
SigLeaves P (In _)           = ⊤
SigLeaves P (out-μ _)        = ⊤
SigLeaves P (Out _)          = ⊤
SigLeaves P (in-ν _)         = ⊤
SigLeaves P (const _ _)      = ⊤

-- plan 0.107 §9 2D: the symbols an IR's SigOp leaves call, leaf by leaf — what
-- the file declares external (minus its own blocks).
leaf-syms : ∀ {A B} → IR A B → List String
leaf-syms (g ∘ f)          = leaf-syms g ++ leaf-syms f
leaf-syms ⟨ f , g ⟩        = leaf-syms f ++ leaf-syms g
leaf-syms (case f g)       = leaf-syms f ++ leaf-syms g
leaf-syms (curry f)        = leaf-syms f
leaf-syms (Cata _ alg)     = leaf-syms alg
leaf-syms (Ana _ coalg)    = leaf-syms coalg
leaf-syms (SigOp si)       = sigop-syms si (cmp-of (sem si))
leaf-syms (Call _)         = []
leaf-syms id               = []
leaf-syms fst              = []
leaf-syms snd              = []
leaf-syms inl              = []
leaf-syms inr              = []
leaf-syms terminal         = []
leaf-syms initial          = []
leaf-syms apply            = []
leaf-syms (In _)           = []
leaf-syms (out-μ _)        = []
leaf-syms (Out _)          = []
leaf-syms (in-ν _)         = []
leaf-syms (const _ _)      = []

-- A property of every collected symbol is one of every SigOp leaf's.
leaf-syms-leaves : ∀ {G : String → Set} {A B} (ir : IR A B) → All G (leaf-syms ir)
                 → SigLeaves (λ si → All G (sigop-syms si (cmp-of (sem si)))) ir
leaf-syms-leaves (g ∘ f)       a = leaf-syms-leaves g (proj₁ (++⁻ (leaf-syms g) a)) , leaf-syms-leaves f (proj₂ (++⁻ (leaf-syms g) a))
leaf-syms-leaves ⟨ f , g ⟩     a = leaf-syms-leaves f (proj₁ (++⁻ (leaf-syms f) a)) , leaf-syms-leaves g (proj₂ (++⁻ (leaf-syms f) a))
leaf-syms-leaves (case f g)    a = leaf-syms-leaves f (proj₁ (++⁻ (leaf-syms f) a)) , leaf-syms-leaves g (proj₂ (++⁻ (leaf-syms f) a))
leaf-syms-leaves (curry f)     a = leaf-syms-leaves f a
leaf-syms-leaves (Cata _ alg)  a = leaf-syms-leaves alg a
leaf-syms-leaves (Ana _ cg)    a = leaf-syms-leaves cg a
leaf-syms-leaves (SigOp si)    a = a
leaf-syms-leaves (Call _)      a = tt
leaf-syms-leaves id            a = tt
leaf-syms-leaves fst           a = tt
leaf-syms-leaves snd           a = tt
leaf-syms-leaves inl           a = tt
leaf-syms-leaves inr           a = tt
leaf-syms-leaves terminal      a = tt
leaf-syms-leaves initial       a = tt
leaf-syms-leaves apply         a = tt
leaf-syms-leaves (In _)        a = tt
leaf-syms-leaves (out-μ _)     a = tt
leaf-syms-leaves (Out _)       a = tt
leaf-syms-leaves (in-ν _)      a = tt
leaf-syms-leaves (const _ _)   a = tt

module _ (G : String → Set) where

  -- the leaf obligations, at the IR's `SigOp` and `Call` nodes
  NodesOK : ∀ {A B} → IR A B → Set
  NodesOK (g ∘ f)          = NodesOK g × NodesOK f
  NodesOK ⟨ f , g ⟩        = NodesOK f × NodesOK g
  NodesOK (case f g)       = NodesOK f × NodesOK g
  NodesOK (curry f)        = NodesOK f
  NodesOK (Cata _ alg)     = NodesOK alg
  NodesOK (Ana _ coalg)    = NodesOK coalg
  NodesOK (Call f)         = G (labelSym (callee (e-fn f)))
  NodesOK (SigOp si)       = All G (sigop-syms si (cmp-of (sem si)))
  NodesOK id               = ⊤
  NodesOK fst              = ⊤
  NodesOK snd              = ⊤
  NodesOK inl              = ⊤
  NodesOK inr              = ⊤
  NodesOK terminal         = ⊤
  NodesOK initial          = ⊤
  NodesOK apply            = ⊤
  NodesOK (In _)           = ⊤
  NodesOK (out-μ _)        = ⊤
  NodesOK (Out _)          = ⊤
  NodesOK (in-ν _)         = ⊤
  NodesOK (const _ _)      = ⊤

  -- A linked IR's calls name table entries; its SigOps are `SigLeaves`'.
  nodes-from : ∀ {σ : ISig} {tbl : List IRFun}
             → (∀ (f : CanonicalName) (A B : IRTy) → LinkedAt tbl f A B → G (labelSym (callee (e-fn f))))
             → ∀ {A B} (ir : IR A B) → Linked σ tbl ir
             → SigLeaves (λ si → All G (sigop-syms si (cmp-of (sem si)))) ir → NodesOK ir
  nodes-from c (g ∘ f)    (lg , lf) (sg , sf) = nodes-from c g lg sg , nodes-from c f lf sf
  nodes-from c ⟨ f , g ⟩  (lf , lg) (sf , sg) = nodes-from c f lf sf , nodes-from c g lg sg
  nodes-from c (case f g) (lf , lg) (sf , sg) = nodes-from c f lf sf , nodes-from c g lg sg
  nodes-from c (curry f)    l s = nodes-from c f l s
  nodes-from c (Cata _ alg) l s = nodes-from c alg l s
  nodes-from c (Ana _ cg)   l s = nodes-from c cg l s
  nodes-from c (Call {A} {B} f) l s = c f A B l
  nodes-from c (SigOp si) l s = s
  nodes-from c id         l s = tt
  nodes-from c fst        l s = tt
  nodes-from c snd        l s = tt
  nodes-from c inl        l s = tt
  nodes-from c inr        l s = tt
  nodes-from c terminal   l s = tt
  nodes-from c initial    l s = tt
  nodes-from c apply      l s = tt
  nodes-from c (In _)     l s = tt
  nodes-from c (out-μ _)  l s = tt
  nodes-from c (Out _)    l s = tt
  nodes-from c (in-ν _)   l s = tt
  nodes-from c (const _ _) l s = tt
