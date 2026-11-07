-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.IRObsCorrect.CataConst.Layout   (plan 0.135 S3, cata M1)
--
-- WHERE THE PARTS OF A `strat-const` CATA SIT. Its text is
--
--     setup (13) ++ call (15) ++ c-jmp end ∷ c-thunk body bb ∷ at ++ c-ret bb ∷ c-label end ∷ []
--
-- (`cata-trace-const`), with the algebra `at` emitted ONCE at frontier 0 and
-- called through the closure record the setup builds. This module reads the
-- cata's three placement premises (`SpanAt`, `LabelsAt`, and the block
-- channel, which is the algebra's own) down to what the run needs: the
-- fetches of the straight rows and the two control rows, the algebra's body
-- block where the call lands, the body's own label resolution, and where the
-- jump over the body goes.
--
-- The 30-row prefix defines no `c-label` (it is straight code, a jump and a
-- marker), so a label the body resolves is resolved 30 rows further on in
-- the cata, and the end label is outside the algebra's label window.
------------------------------------------------------------------------

open import Once.Spec.Name using (CanonicalName)

import Data.List as DL
open import Once.Denotation.Program using (IRFun)
module Once.CCC.Codegen.IRObsCorrect.CataConst.Layout (o : CanonicalName) (tbl : DL.List IRFun) where

open import Once.CCC.Codegen.IRObsCorrect.Machine o tbl
open import Once.CCC.Codegen.IRObsCorrect.Resusp.Base o tbl using (module ResuspBaseC)
open import Once.CCC.Codegen.IRToTrace o
  using (rec-count; cata-strategy; CataStrategy; strat-const; strat-box; cata-dispatch; cata-call-setup; cata-call; cata-call-from; cata-body;
         const-strategy; box-fun)
open import Once.CCC.Codegen.IRObsCorrect.CataConst.Steps o tbl using (Head; h-mov; h-box; head-instr; head-strat)
open import Once.CCC.Codegen.IRObsCorrect.CataConst.Call o tbl using (module CataCallC)
open import Once.CCC.Codegen.FlatLayout using (Kind; word; flat; kind; lkind; lsz; skind; ssize; kind-skind; size-ssize; get; get-All; put; put-All)
open import Once.CCC.Codegen.Size using (size)
open import Relation.Nullary using (¬_)
open import Once.Spec.Type using (Fun)
open import Once.CCC.Machine.MuRep using (mu-rep; mu-box; Unboxed)
open import Data.Bool using (Bool)
open import Once.IRTy using (wf-K; wf-Id; wf-Sum; wf-Prod; base-Int; base-Float; base-Unit; base-Void; base-Prod; base-Sum)
import Data.List.Relation.Unary.All as All
open import Once.CCC.Codegen.LabelResolve o using (module Resolve)
open import Once.CCC.Codegen.LabelScope o using (labels-in)
open import Once.CCC.Codegen.FlatStepLemmas using (module FlatStepsAPI)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.SMCore using (AbstractTrace; instr-ctrl; c-jmp; c-label; c-ret; c-thunk; block-layout; instr-call-closure)
open import Once.CCC.Label using (ℓ; LabelId)
open import Once.IRTy using (IRTy; IRFunctor; WellFormedFI; ⟦_⟧TI; ⌈_⌉F)
import Once.IRTy as IRTy′
import Data.Nat as ℕ
open import Data.List.Relation.Unary.All using () renaming (_∷_ to _∷ᴬ_; [] to []ᴬ)
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:+_; con; _:=_)

-- the end pc, as arithmetic
end-pc : ∀ (a b : ℕ) → suc ((31 + a) + b) ≡ (30 + (a + 2)) + b
end-pc = solve 2 (λ a b → con 1 :+ ((con 31 :+ a) :+ b) := (con 30 :+ (a :+ con 2)) :+ b) refl

-- The classifier's `strat-const` and `strat-box` are "no recursive position".
const-rc : ∀ G (h : Head) → cata-strategy G ≡ head-strat h → rec-count G ≡ 0
const-rc G h eq with rec-count G | eq
const-rc G h eq | zero  | _ = refl
const-rc G h-mov eq | suc _ | ()
const-rc G h-box eq | suc _ | ()

-- …and which of the two is the classifier's box test (D366).
head-box : Head → Bool
head-box h-mov = false
head-box h-box = true

strat-box-fun : ∀ G (h : Head) → cata-strategy G ≡ head-strat h → box-fun G ≡ head-box h
strat-box-fun G h eq with rec-count G | eq
strat-box-fun G h eq | zero | e = cs-inv (box-fun G) h e
  where cs-inv : ∀ b (h′ : Head) → const-strategy b ≡ head-strat h′ → b ≡ head-box h′
        cs-inv true  h-mov ()
        cs-inv true  h-box refl = refl
        cs-inv false h-mov refl = refl
        cs-inv false h-box ()
strat-box-fun G h-mov eq | suc _ | ()
strat-box-fun G h-box eq | suc _ | ()

-- the box test, on the IR side, is `MuRep`'s
unboxed-of : ∀ {F} (wf : WellFormedFI F) → box-fun ⌈ F ⌉F ≡ false → Unboxed F
unboxed-of (wf-K base-Int)        ()
unboxed-of (wf-K base-Float)      ()
unboxed-of (wf-K base-Unit)       _ = tt
unboxed-of (wf-K base-Void)       _ = tt
unboxed-of (wf-K (base-Prod a b)) _ = tt
unboxed-of (wf-K (base-Sum a b))  _ = tt
unboxed-of wf-Id                  _ = tt
unboxed-of (wf-Sum f g)           _ = tt
unboxed-of (wf-Prod f g)          _ = tt

boxed-of : ∀ {F} (wf : WellFormedFI F) → box-fun ⌈ F ⌉F ≡ true → mu-rep F ≡ mu-box
boxed-of (wf-K base-Int)        _ = refl
boxed-of (wf-K base-Float)      _ = refl
boxed-of (wf-K base-Unit)       ()
boxed-of (wf-K base-Void)       ()
boxed-of (wf-K (base-Prod a b)) ()
boxed-of (wf-K (base-Sum a b))  ()
boxed-of wf-Id                  ()
boxed-of (wf-Sum f g)           ()
boxed-of (wf-Prod f g)          ()

-- …and the dispatch at either is the same skeleton, its first call row the head's.
head-dispatch : ∀ (h : Head) (E A : IRTy) (G : Fun 0) (bb n l1 : ℕ) (at : AbstractTrace)
              → proj₂ (proj₂ (cata-dispatch E A G (head-strat h) bb n l1 at))
              ≡ cata-call-setup E n (n ℕ.+ 1) (n ℕ.+ 2) l1 ++
                (cata-call-from (head-instr h) E (lkind G word) (lsz G 1) n (n ℕ.+ 1) (n ℕ.+ 2) (n ℕ.+ 3) ++ cata-body l1 (l1 ℕ.+ 1) bb at)
head-dispatch h-mov E A G bb n l1 at = refl
head-dispatch h-box E A G bb n l1 at = refl

-- the layer's kind and size, by the IR's rule and by the Spec functor's
lkind-eq : ∀ (F : IRFunctor) (X : IRTy) → kind X ≡ word → kind (⟦ F ⟧TI X) ≡ lkind ⌈ F ⌉F word
lkind-eq (IRTy′.K A) X _ = kind-skind A
lkind-eq IRTy′.Id    X e = e
lkind-eq (F IRTy′.⊕ G) X _ = refl
lkind-eq (F IRTy′.⊗ G) X _ = refl

lsz-eq : ∀ (F : IRFunctor) (X : IRTy) → size X ≡ 1 → size (⟦ F ⟧TI X) ≡ lsz ⌈ F ⌉F 1
lsz-eq (IRTy′.K A) X _ = size-ssize A
lsz-eq IRTy′.Id    X e = e
lsz-eq (F IRTy′.⊕ G) X e = cong suc (cong₂ ℕ._⊔_ (lsz-eq F X e) (lsz-eq G X e))
lsz-eq (F IRTy′.⊗ G) X e = cong₂ ℕ._+_ (lsz-eq F X e) (lsz-eq G X e)

module CataLayoutC {FS : FrameSemantics} where

  open Core {FS}
  open ResuspBaseC {FS} using (span-take; span-drop; labels-take; labels-drop)
  open CataCallC {FS} using (callK; call-shape)
  open Resolve {FS} using (NoLabel; noLabel-outside; fl-hit)
  open FlatStepsAPI {FS} using (fl-go-skip)
  open import Once.CCC.Codegen.IRObsCorrect.Get o tbl using (module GetC)
  open GetC {FS} using (get-len)

  nl-head : ∀ (h : Head) (m : LabelId) → NoLabel m (head-instr h ∷ [])
  nl-head h-mov m = (λ ()) ∷ᴬ []ᴬ
  nl-head h-box m = (λ ()) ∷ᴬ []ᴬ

  module Text {F : IRFunctor} (wf : WellFormedFI F) {E C : IRTy} (alg : IR (E IRTy′.* ⟦ F ⟧TI C) C) (n l : ℕ) (h : Head) where

    bb l1 : ℕ
    bb = proj₁ (ir-to-trace' 0 l alg)
    l1 = proj₁ (proj₂ (ir-to-trace' 0 l alg))

    at : AbstractTrace
    at = emitted 0 l alg

    endL : LabelId
    endL = ℓ o (l1 ℕ.+ 1)

    -- the layer at the call: the μ's own layer
    L : IRTy
    L = ⟦ F ⟧TI (IRTy′.μ-type F)

    lk : Kind
    lk = lkind ⌈ F ⌉F word
    ls : ℕ
    ls = lsz ⌈ F ⌉F 1

    lkeq : lk ≡ kind L
    lkeq = sym (lkind-eq F (IRTy′.μ-type F) refl)
    lseq : ls ≡ size L
    lseq = sym (lsz-eq F (IRTy′.μ-type F) refl)

    setup callK′ call body post text : AbstractTrace
    setup  = cata-call-setup E n (n ℕ.+ 1) (n ℕ.+ 2) l1
    callK′ = callK (head-instr h) E L n
    call   = callK′ ++ instr-call-closure ∷ []
    body   = cata-body l1 (l1 ℕ.+ 1) bb at
    post   = instr-ctrl (c-ret bb) ∷ instr-ctrl (c-label endL) ∷ []
    text   = setup ++ (call ++ body)

    CK : ℕ
    CK = length callK′

    -- `ir-to-trace'`'s dispatch, at the strategy this case is about
    emitted-eq : cata-strategy ⌈ F ⌉F ≡ head-strat h → emitted n l (Cata wf alg) ≡ text
    emitted-eq eq =
      trans (cong (λ st → proj₂ (proj₂ (cata-dispatch E C ⌈ F ⌉F st bb n l1 at))) eq)
     (trans (head-dispatch h E C ⌈ F ⌉F bb n l1 at)
            (cong (λ t → setup ++ (t ++ body)) (call-shape (head-instr h) E L lk ls n lkeq lseq)))

    len-setup : length setup ≡ 13
    len-setup = trans (length-++ (get E 0) {_}) (cong (ℕ._+ 12) (get-len E 0))

    len-text : length text ≡ (13 ℕ.+ (CK ℕ.+ 1)) ℕ.+ (4 ℕ.+ length at)
    len-text = trans (length-++ setup {call ++ body})
                 (cong₂ ℕ._+_ len-setup
                   (trans (length-++ call {body})
                          (cong₂ ℕ._+_ (length-++ callK′ {instr-call-closure ∷ []})
                                       (cong (2 ℕ.+_) (length-++ at {post})))))
               ∙ arith CK (length at)
      where _∙_ = trans
            arith : ∀ c a → 13 ℕ.+ ((c ℕ.+ 1) ℕ.+ (2 ℕ.+ (a ℕ.+ 2))) ≡ (13 ℕ.+ (c ℕ.+ 1)) ℕ.+ (4 ℕ.+ a)
            arith = solve 2 (λ c a → con 13 :+ ((c :+ con 1) :+ (con 2 :+ (a :+ con 2)))
                                   := (con 13 :+ (c :+ con 1)) :+ (con 4 :+ a)) refl

    -- the end label is above the algebra's window `[l , l1)`
    no-end : NoLabel endL at
    no-end = noLabel-outside endL at (labels-in alg 0 l)
               (λ w → <-irrefl refl (<-≤-trans (proj₂ w) (m≤m+n l1 1)))

    -- the prefix before the algebra's body defines no label
    jt : AbstractTrace
    jt = instr-ctrl (c-jmp endL) ∷ instr-ctrl (c-thunk (ℓ o l1) bb) ∷ []

    pre : AbstractTrace
    pre = setup ++ (call ++ jt)

    shape′ : text ≡ pre ++ (at ++ post)
    shape′ = sym (trans (++-assoc setup (call ++ jt) (at ++ post)) (cong (setup ++_) (++-assoc call jt (at ++ post))))

    no-pre : ∀ m → NoLabel m pre
    no-pre m =
      ++⁺ (++⁺ (get-All {λ i → ¬ (label-of? i ≡ just m)} E 0 (λ _ ()) (λ _ ()) (λ ()))
               ((λ ()) ∷ᴬ (λ ()) ∷ᴬ (λ ()) ∷ᴬ (λ ()) ∷ᴬ (λ ()) ∷ᴬ (λ ()) ∷ᴬ (λ ()) ∷ᴬ (λ ()) ∷ᴬ (λ ()) ∷ᴬ (λ ()) ∷ᴬ (λ ()) ∷ᴬ (λ ()) ∷ᴬ []ᴬ))
          (++⁺ (++⁺ (++⁺ (All.head (nl-head h m) ∷ᴬ (λ ()) ∷ᴬ (λ ()) ∷ᴬ (λ ()) ∷ᴬ
                          ++⁺ (put-All {λ i → ¬ (label-of? i ≡ just m)} E (n ℕ.+ 2) (n ℕ.+ 3) 0 (λ ()) (λ ()) (λ ()) (λ _ ()) (λ _ ()))
                              (++⁺ (put-All {λ i → ¬ (label-of? i ≡ just m)} L (n ℕ.+ 1) (n ℕ.+ 3) (size E) (λ ()) (λ ()) (λ ()) (λ _ ()) (λ _ ()))
                                   ((λ ()) ∷ᴬ (λ ()) ∷ᴬ []ᴬ)))
                         ((λ ()) ∷ᴬ (λ ()) ∷ᴬ (λ ()) ∷ᴬ []ᴬ))
                    ((λ ()) ∷ᴬ []ᴬ))
               ((λ ()) ∷ᴬ (λ ()) ∷ᴬ []ᴬ))

    LP : ℕ
    LP = length pre

    len-call : length call ≡ CK ℕ.+ 1
    len-call = length-++ callK′ {instr-call-closure ∷ []}

    len-pre : LP ≡ 13 ℕ.+ ((CK ℕ.+ 1) ℕ.+ 2)
    len-pre = trans (length-++ setup {call ++ jt})
                    (cong₂ ℕ._+_ len-setup (trans (length-++ call {jt}) (cong (ℕ._+ 2) len-call)))

    -- the end label: after the prefix, the body, and its return
    end-scan : find-label text endL ≡ just (suc ((0 ℕ.+ LP) ℕ.+ length at))
    end-scan = trans (cong (λ t → fl-go t endL 0) shape′)
              (trans (fl-go-skip pre (at ++ post) endL 0 (no-pre endL))
              (trans (fl-go-skip at post endL (0 ℕ.+ LP) no-end)
                     (fl-hit endL [] (suc ((0 ℕ.+ LP) ℕ.+ length at)))))

    ------------------------------------------------------------------
    -- …and in the program.
    ------------------------------------------------------------------
    module At (prog : AbstractTrace) (base : ℕ) (span : SpanAt prog base text) (la : LabelsAt prog base text) where

      span-setup : SpanAt prog base setup
      span-setup = span-take prog setup {call ++ body} base span

      span-cb : SpanAt prog (13 ℕ.+ base) (call ++ body)
      span-cb = subst (λ z → SpanAt prog (z ℕ.+ base) (call ++ body)) len-setup
                      (span-drop prog setup {call ++ body} base span)

      span-call : SpanAt prog (13 ℕ.+ base) call
      span-call = span-take prog call {body} (13 ℕ.+ base) span-cb

      span-callK : SpanAt prog (13 ℕ.+ base) callK′
      span-callK = span-take prog callK′ {instr-call-closure ∷ []} (13 ℕ.+ base) span-call

      fetch-cc : fetch prog (CK ℕ.+ (13 ℕ.+ base)) ≡ just instr-call-closure
      fetch-cc = span-drop prog callK′ {instr-call-closure ∷ []} (13 ℕ.+ base) span-call 0 _ refl

      span-body : SpanAt prog ((CK ℕ.+ 1) ℕ.+ (13 ℕ.+ base)) body
      span-body = subst (λ z → SpanAt prog (z ℕ.+ (13 ℕ.+ base)) body) len-call
                        (span-drop prog call {body} (13 ℕ.+ base) span-cb)

      fetch-jmp : fetch prog ((CK ℕ.+ 1) ℕ.+ (13 ℕ.+ base)) ≡ just (instr-ctrl (c-jmp endL))
      fetch-jmp = span-body 0 _ refl

      fetch-thunk : fetch prog (suc ((CK ℕ.+ 1) ℕ.+ (13 ℕ.+ base))) ≡ just (instr-ctrl (c-thunk (ℓ o l1) bb))
      fetch-thunk = span-body 1 _ refl

      body-span : SpanAt prog (suc ((CK ℕ.+ 1) ℕ.+ (13 ℕ.+ base))) (block-layout (ℓ o l1 , bb , at))
      body-span = span-take prog (block-layout (ℓ o l1 , bb , at)) {instr-ctrl (c-label endL) ∷ []} (suc ((CK ℕ.+ 1) ℕ.+ (13 ℕ.+ base)))
                    (subst (λ t → SpanAt prog (suc ((CK ℕ.+ 1) ℕ.+ (13 ℕ.+ base))) (instr-ctrl (c-thunk (ℓ o l1) bb) ∷ t))
                           (sym (++-assoc at (instr-ctrl (c-ret bb) ∷ []) (instr-ctrl (c-label endL) ∷ [])))
                           (span-drop prog (instr-ctrl (c-jmp endL) ∷ []) {instr-ctrl (c-thunk (ℓ o l1) bb) ∷ (at ++ post)}
                              ((CK ℕ.+ 1) ℕ.+ (13 ℕ.+ base)) span-body))

      span′ : SpanAt prog base (pre ++ (at ++ post))
      span′ = subst (SpanAt prog base) shape′ span

      la′ : LabelsAt prog base (pre ++ (at ++ post))
      la′ = subst (LabelsAt prog base) shape′ la

      body-labels : LabelsAt prog (LP ℕ.+ base) at
      body-labels = labels-take prog at {post} (LP ℕ.+ base)
                      (labels-drop prog pre {at ++ post} base la′ (λ m _ _ → no-pre m))

      fetch-end : fetch prog (suc (length at ℕ.+ (LP ℕ.+ base))) ≡ just (instr-ctrl (c-label endL))
      fetch-end = span-drop prog at {post} (LP ℕ.+ base) (span-drop prog pre {at ++ post} base span′) 1 _ refl

      end-label : find-label prog endL ≡ just (suc ((0 ℕ.+ LP) ℕ.+ length at) ℕ.+ base)
      end-label = la endL (suc ((0 ℕ.+ LP) ℕ.+ length at)) end-scan
