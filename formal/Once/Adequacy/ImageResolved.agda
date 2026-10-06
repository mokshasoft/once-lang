-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.ImageResolved — plan 0.107 phase d, layer 2 assembled: EVERY
-- SYMBOL THE PROGRAM IMAGE REFERENCES IS DEFINED, OR AN INTERPRETATION'S.
--
-- The image is `_start`, `main`'s unit (ending in the silent stop), and each
-- table entry's marker and unit. `RefsClosed` closes each unit's local
-- references against the image's definitions; the global ones are the leaves'
-- (`NodesOK`): a call names a table entry, whose marker the image carries
-- (linkedness); a SigOp names a block or an extern — `SigLeaves`, the one fact
-- still taken as a premise here (`ImageWF.prog-sigops`).
------------------------------------------------------------------------

module Once.Adequacy.ImageResolved where

open import Data.Nat using (ℕ; suc)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.All using (All; []; _∷_) renaming (map to All-map)
open import Data.Maybe using (just)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.String using (String)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥-elim)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)
open import Relation.Nullary using (yes; no)

open import Once.CanonicalName using (CanonicalName; _≟ᶜ_)
open import Once.IR using (IR)
open import Once.IRTy using (IRTy; ⌊_⌋; _≟IRTy_)
open import Once.Type using (Unit)
open import Once.CCC.Label using (callee; e-fn; labelSym)
open import Once.SigOp.Info using (sem)
open import Once.Arith.SigOp.Compare using (cmp-of)
open import Once.CCC.Machine.SMCore using (AbstractTrace; AbstractInstr; instr-ctrl; c-entry; c-label; c-jmp;
                                          blocks-layout; link; link-top; unit)
open import Once.Denotation.Program using (IRFun; fname; fdom; fcod; fbody; irProgram; table; main;
                                           LinkedAt; LinkedAt-at; LinkedProgram)
open import Once.CCC.Codegen.ImageSymbols using (instr-defs; adefs; arefs; heap-symbol)
open import Once.CCC.Codegen.NodesOK using (NodesOK; SigLeaves; sigop-syms; nodes-from)
import Once.CCC.Codegen.RefsClosed as RC
import Once.CCC.Codegen.IRToTrace as IT
import Once.CCC.Codegen.LabelScope as LS
import Once.CCC.Codegen.SlotBudget as SB
open import Once.CCC.Codegen.ProgramImage using (fns-image; fn-image; fn-next; top-done)
import Once.Compile as C
open import Once.Compile using (Module; moduleToIR; moduleTable)
open import Once.Compile using (externs-of)
open import Once.Adequacy.ImageWF using (prog-defs; Resolved; ProgG; ProgP; prog-sigops)
open import Once.Adequacy.ProgramLinked using (moduleToProgram-linked)
open import Once.Spec.Module using (moduleSig)
open import Once.Adequacy.SourceTrace using (rewrite-program-linked)

------------------------------------------------------------------------
-- Generic facts.
------------------------------------------------------------------------

-- every instruction's definitions are among its trace's
defd-self : ∀ (t : AbstractTrace) {i} → i ∈ t → ∀ {s} → s ∈ instr-defs i → s ∈ adefs t
defd-self (j ∷ js) (here refl) m = ∈-++⁺ˡ m
defd-self (j ∷ js) (there mi) m = ∈-++⁺ʳ (instr-defs j) (defd-self js mi m)

-- a linked call names an entry of the table
linked-entry : ∀ (tbl : List IRFun) (f : CanonicalName) (A B : IRTy) → LinkedAt tbl f A B
             → Σ[ e ∈ IRFun ] (e ∈ tbl × fname e ≡ f)
linked-entry []       f A B ()
linked-entry (e ∷ es) f A B lk = at (fname e ≟ᶜ f) (fdom e ≟IRTy A) (fcod e ≟IRTy B) lk
  where
    rest : LinkedAt es f A B → Σ[ e′ ∈ IRFun ] (e′ ∈ e ∷ es × fname e′ ≡ f)
    rest l with linked-entry es f A B l
    ... | e′ , m , q = e′ , there m , q
    at : ∀ d₁ d₂ d₃ → LinkedAt-at e es f A B d₁ d₂ d₃ → Σ[ e′ ∈ IRFun ] (e′ ∈ e ∷ es × fname e′ ≡ f)
    at (yes q) (yes _) (yes _) _ = e , here refl , q
    at (yes _) (yes _) (no _)  l = rest l
    at (yes _) (no _)  _       l = rest l
    at (no _)  _       _       l = rest l

-- …and every table entry's marker is in the functions' image
entry∈fns : ∀ (l : ℕ) (tbl : List IRFun) {e : IRFun} → e ∈ tbl
          → Σ[ b ∈ ℕ ] (instr-ctrl (c-entry (e-fn (fname e)) b) ∈ fns-image l tbl)
entry∈fns l (e ∷ es) (here refl) = IT.ir-stack-budget-from (fname e) l (fbody e) , here refl
entry∈fns l (e ∷ es) (there m) with entry∈fns (fn-next l e) es m
... | b , mem = b , ∈-++⁺ʳ (fn-image l e) mem

------------------------------------------------------------------------
-- THE PROGRAM.
------------------------------------------------------------------------

module Prog (m : Module) (ir : IR ⌊ Unit ⌋ ⌊ Unit ⌋) (mi : moduleToIR m ≡ just ir) where

  p   = irProgram (moduleTable m) ir
  rp  = C.rewrite-program p
  eo  = C.entry-owner
  D   = prog-defs p
  ext = externs-of (irProgram (moduleTable m) ir)
  img = C.image-of p

  G : String → Set
  G = ProgG m ir

  P : ∀ {A B} → Once.SigOp.Info.SigOpInfo A B → Set
  P = ProgP m ir

  inD : ∀ {s} → s ∈ adefs img → s ∈ D
  inD x = there (there (∈-++⁺ˡ x))

  -- the image's definitions are `D`'s
  d-img : ∀ {i} → i ∈ img → ∀ {s} → s ∈ instr-defs i → s ∈ D
  d-img mem ms = inD (defd-self img mem ms)

  main′ = main rp
  X     = IT.ir-to-trace' eo 0 0 main′
  T     = LS.trace-of eo X
  L     = blocks-layout (SB.bodies-of eo X)
  done  = top-done eo rp
  LT    = link-top done (IT.ir-to-unit eo main′)
  FI    = fns-image (suc (IT.ir-next-label eo 0 main′)) (table rp)

  LT⊆ : ∀ {i} → i ∈ LT → i ∈ img
  LT⊆ x = there (∈-++⁺ˡ x)

  FI⊆ : ∀ {i} → i ∈ FI → i ∈ img
  FI⊆ x = there (∈-++⁺ʳ LT x)

  -- a call names a table entry, and the image carries its marker
  call-G : ∀ (f : CanonicalName) (A B : IRTy) → LinkedAt (table rp) f A B → G (labelSym (callee (e-fn f)))
  call-G f A B lk with linked-entry (table rp) f A B lk
  ... | e , em , refl with entry∈fns (suc (IT.ir-next-label eo 0 main′)) (table rp) em
  ...   | b , mem = inj₁ (d-img (FI⊆ mem) (here refl))

  module _ (sl-main : SigLeaves P main′) (sl-tbl : All (λ e → SigLeaves P (fbody e)) (table rp)) where

    lk = rewrite-program-linked p (moduleToProgram-linked m ir mi)

    closes-LT : RC.Closes eo G D LT
    closes-LT =
      RC.closes-++ eo G T (instr-ctrl (c-label done) ∷ instr-ctrl (c-jmp done) ∷ L) (proj₁ cl)
        (inj₁ (d-img (LT⊆ (∈-++⁺ʳ T (here refl))) (here refl)) ∷ proj₂ cl)
      where
        cl = RC.close eo G main′ 0 0
               (λ x → d-img (LT⊆ (RC.++-⊆ eo T L (∈-++⁺ˡ) (λ y → ∈-++⁺ʳ T (there (there y))) x)))
               (nodes-from G call-G main′ (proj₁ lk) sl-main)

    closes-FI : ∀ (l : ℕ) (es : List IRFun)
              → (∀ {i} → i ∈ fns-image l es → i ∈ img)
              → All (λ e → Once.Denotation.Program.Linked (moduleSig m) (table rp) (fbody e)) es
              → All (λ e → SigLeaves P (fbody e)) es
              → RC.Closes eo G D (fns-image l es)
    closes-FI l []       sub _          _          = []
    closes-FI l (e ∷ es) sub (lke ∷ lks) (sle ∷ sls) =
      RC.closes-++ eo G (fn-image l e) (fns-image (fn-next l e) es)
        (RC.closes-++ eo G Te (Once.CCC.Machine.SMCore.instr-ctrl (Once.CCC.Machine.SMCore.c-ret _) ∷ Le)
                      (proj₁ cl) (proj₂ cl))
        (closes-FI (fn-next l e) es (λ x → sub (∈-++⁺ʳ (fn-image l e) x)) lks sls)
      where
        Y  = IT.ir-to-trace' (fname e) 0 l (fbody e)
        Te = LS.trace-of (fname e) Y
        Le = blocks-layout (SB.bodies-of (fname e) Y)
        unit⊆ : ∀ {i} → i ∈ Te ++ Le → i ∈ fn-image l e
        unit⊆ = RC.++-⊆ eo Te Le (λ y → there (∈-++⁺ˡ y)) (λ y → there (∈-++⁺ʳ Te (there y)))
        cl = RC.close (fname e) G (fbody e) 0 l
               (λ x → d-img (sub (∈-++⁺ˡ (unit⊆ x))))
               (nodes-from G call-G (fbody e) lke sle)

    closes-img : RC.Closes eo G D img
    closes-img =
      inj₁ (here refl) ∷
      RC.closes-++ eo G LT FI closes-LT (closes-FI (suc (IT.ir-next-label eo 0 main′)) (table rp) FI⊆ (proj₂ lk) sl-tbl)

    resolved : Resolved D ext (arefs img)
    resolved = All-map flat closes-img
      where
        flat : ∀ {s} → s ∈ D ⊎ G s → s ∈ D ⊎ s ∈ ext
        flat (inj₁ x)        = inj₁ x
        flat (inj₂ (inj₁ x)) = inj₁ x
        flat (inj₂ (inj₂ y)) = inj₂ y

-- THE THEOREM (was `ImageWF.prog-resolved`, a postulate).
prog-resolved : ∀ (m : Module) (ir : IR ⌊ Unit ⌋ ⌊ Unit ⌋) (mi : moduleToIR m ≡ just ir)
              → Resolved (prog-defs (irProgram (moduleTable m) ir)) (externs-of (irProgram (moduleTable m) ir))
                         (arefs (C.image-of (irProgram (moduleTable m) ir)))
prog-resolved m ir mi = Prog.resolved m ir mi (proj₁ (prog-sigops m ir mi)) (proj₂ (prog-sigops m ir mi))
