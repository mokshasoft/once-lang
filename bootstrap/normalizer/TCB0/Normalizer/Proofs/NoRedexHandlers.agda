------------------------------------------------------------------------
-- Normalize.NoRedexHandlers: NoRedex proofs for handlers
--
-- NoRedex proofs for:
-- - Simple handlers (just rebuilds)
-- - Complex handle-comp (via caseWithCtx)
-- - distrib and caseWithCtx infrastructure
-- - is-id-dispatch and is-id
------------------------------------------------------------------------

module normalizer.TCB0.Normalizer.Proofs.NoRedexHandlers where

open import normalizer.TCB0.Normalizer.Handlers public
open import normalizer.TCB0.Normalizer.Proofs.NoRedexRebuild public

------------------------------------------------------------------------
-- NoRedex proofs for simple handlers (just rebuilds)
------------------------------------------------------------------------

nr-handle-id : NoRedex handle-id
nr-handle-id = nr-rebuild-0

nr-handle-fst : NoRedex handle-fst
nr-handle-fst = nr-rebuild-2

nr-handle-snd : NoRedex handle-snd
nr-handle-snd = nr-rebuild-3

nr-handle-pair : NoRedex handle-pair
nr-handle-pair = nr-rebuild-4

nr-handle-inl : NoRedex handle-inl
nr-handle-inl = nr-rebuild-5

nr-handle-inr : NoRedex handle-inr
nr-handle-inr = nr-rebuild-6

nr-handle-case : NoRedex handle-case
nr-handle-case = nr-rebuild-7

nr-handle-terminal : NoRedex handle-terminal
nr-handle-terminal = nr-rebuild-8

nr-handle-initial : NoRedex handle-initial
nr-handle-initial = nr-rebuild-9

nr-handle-In : NoRedex handle-In
nr-handle-In = nr-rebuild-10

nr-handle-Out : NoRedex handle-Out
nr-handle-Out = nr-rebuild-11

nr-handle-cata : NoRedex handle-cata
nr-handle-cata = nr-rebuild-12

nr-handle-curry : NoRedex handle-curry
nr-handle-curry = nr-rebuild-13

nr-handle-apply : NoRedex handle-apply
nr-handle-apply = nr-rebuild-14

------------------------------------------------------------------------
-- NoRedex proofs for distrib infrastructure
------------------------------------------------------------------------

private
  -- Helper: swap = ⟨ snd, fst ⟩ is NoRedex
  nr-swap : ∀ {A B} → NoRedex (⟨ snd {A} {B} , fst ⟩)
  nr-swap = nr-pair nr-snd nr-fst

  -- inl/inr ∘ swap
  nr-inl-swap : ∀ {A B C} → NoRedex (inl {A * B} {C} ∘ ⟨ snd , fst ⟩)
  nr-inl-swap = nr-comp nr-inl nr-swap (sc-neither nis-inl nis-pair nas-inl)

  nr-inr-swap : ∀ {A B C} → NoRedex (inr {C} {A * B} ∘ ⟨ snd , fst ⟩)
  nr-inr-swap = nr-comp nr-inr nr-swap (sc-neither nis-inr nis-pair nas-inr)

  -- curry of the above
  nr-curry-inl-swap : ∀ {A B C} → NoRedex (curry (inl {A * B} {C} ∘ ⟨ snd , fst ⟩))
  nr-curry-inl-swap = nr-curry nr-inl-swap

  nr-curry-inr-swap : ∀ {A B C} → NoRedex (curry (inr {C} {A * B} ∘ ⟨ snd , fst ⟩))
  nr-curry-inr-swap = nr-curry nr-inr-swap

  -- The case in distrib
  nr-distrib-case : ∀ {P A B} → NoRedex ([ curry (inl {P * A} {P * B} ∘ ⟨ snd , fst ⟩) , curry (inr ∘ ⟨ snd , fst ⟩) ])
  nr-distrib-case = nr-case nr-curry-inl-swap nr-curry-inr-swap

  -- case ∘ snd
  nr-distrib-case-snd : ∀ {P A B} → NoRedex ([ curry (inl {P * A} {P * B} ∘ ⟨ snd , fst ⟩) , curry (inr ∘ ⟨ snd , fst ⟩) ] ∘ snd {P} {A + B})
  nr-distrib-case-snd = nr-comp nr-distrib-case nr-snd (sc-neither nis-case nis-snd nas-case)

  -- The pair in distrib: ⟨ case ∘ snd, fst ⟩
  nr-distrib-pair : ∀ {P A B} → NoRedex (⟨ [ curry (inl {P * A} {P * B} ∘ ⟨ snd , fst ⟩) , curry (inr ∘ ⟨ snd , fst ⟩) ] ∘ snd , fst ⟩)
  nr-distrib-pair = nr-pair nr-distrib-case-snd nr-fst

-- distrib = apply ∘ pair
-- For apply ∘ pair, we need sc-apply since f=apply
-- The pair is not ⟨curry _, _⟩ since fst component is a composition (case ∘ snd)
nr-distrib : ∀ {P A B} → NoRedex (distrib {P} {A} {B})
nr-distrib {P} {A} {B} = nr-comp nr-apply nr-distrib-pair (sc-apply nis-pair (ncpl-pair ncs-comp))

-- caseWithCtx l r = [ l, r ] ∘ distrib
nr-caseWithCtx : ∀ {P A B D} {l : Term (P * A) D} {r : Term (P * B) D} →
                 NoRedex l → NoRedex r → NoRedex (caseWithCtx l r)
nr-caseWithCtx nrl nrr = nr-comp (nr-case nrl nrr) nr-distrib (sc-neither nis-case nis-comp nas-case)

------------------------------------------------------------------------
-- NoRedex proofs for is-id-dispatch
------------------------------------------------------------------------

private
  -- is-id-dispatch is a 15-way nested case (positions 0-14)
  nr-is-id-dispatch : NoRedex is-id-dispatch
  nr-is-id-dispatch =
    nr-case nr-ret-yes
      (nr-case nr-ret-no-1
        (nr-case nr-ret-no-2
          (nr-case nr-ret-no-3
            (nr-case nr-ret-no-4
              (nr-case nr-ret-no-5
                (nr-case nr-ret-no-6
                  (nr-case nr-ret-no-7
                    (nr-case nr-ret-no-8
                      (nr-case nr-ret-no-9
                        (nr-case nr-ret-no-10
                          (nr-case nr-ret-no-11
                            (nr-case nr-ret-no-12
                              (nr-case nr-ret-no-13 nr-ret-no-14)))))))))))))

-- is-id = is-id-dispatch ∘ Out
nr-is-id' : NoRedex is-id
nr-is-id' = nr-comp nr-is-id-dispatch nr-Out (sc-neither nis-case nis-Out nas-case)

------------------------------------------------------------------------
-- NoRedex proofs for handle-comp infrastructure
------------------------------------------------------------------------

private
  -- prep-check-f-id = ⟨ snd, is-id ∘ fst ⟩
  nr-is-id-fst : NoRedex (is-id ∘ fst {TermCode'} {TermCode'})
  nr-is-id-fst = nr-comp nr-is-id' nr-fst (sc-neither nis-comp nis-fst nas-comp)

  nr-prep-check-f-id : NoRedex prep-check-f-id
  nr-prep-check-f-id = nr-pair nr-snd nr-is-id-fst

  -- comp-f-is-id = fst
  nr-comp-f-is-id : NoRedex comp-f-is-id
  nr-comp-f-is-id = nr-fst

  -- prep-check-g-id = ⟨ snd, is-id ∘ fst ⟩ (same as prep-check-f-id)
  nr-prep-check-g-id : NoRedex prep-check-g-id
  nr-prep-check-g-id = nr-pair nr-snd nr-is-id-fst

  -- comp-g-is-id = fst
  nr-comp-g-is-id : NoRedex comp-g-is-id
  nr-comp-g-is-id = nr-fst

  -- comp-fallback = rebuild-1
  nr-comp-fallback : NoRedex comp-fallback
  nr-comp-fallback = nr-rebuild-1

  -- check-g-handler = caseWithCtx comp-g-is-id comp-fallback ∘ prep-check-g-id
  nr-check-g-handler : NoRedex check-g-handler
  nr-check-g-handler = nr-comp (nr-caseWithCtx nr-comp-g-is-id nr-comp-fallback) nr-prep-check-g-id (sc-neither nis-comp nis-pair nas-comp)

-- handle-comp = caseWithCtx comp-f-is-id check-g-handler ∘ prep-check-f-id
nr-handle-comp : NoRedex handle-comp
nr-handle-comp = nr-comp (nr-caseWithCtx nr-comp-f-is-id nr-check-g-handler) nr-prep-check-f-id (sc-neither nis-comp nis-pair nas-comp)
