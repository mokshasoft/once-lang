-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.IRObsCorrect.Apply
--
-- D200: `apply` — the sixteen-instruction setup, the call, and the hand-off
-- to `BlockRuns.closures` (D188).
------------------------------------------------------------------------

open import Once.CanonicalName using (CanonicalName)

module Once.CCC.Codegen.IRObsCorrect.Apply (o : CanonicalName) where

open import Once.CCC.Codegen.IRObsCorrect.Machine o

import Once.CCC.FrameSemantics
import Once.CCC.Machine.SMPrimitives
import Once.IRTy
import Once.IR
import Once.CCC.Eval as Ev
import Once.Semantics.Machine as EvV
import Once.CCC.Machine.ReadTypedAdequate as RTA
import Once.Denotation.DenotTrace as DT
import Once.Denotation.TraceMonad as TM

module ApplyC {FS : FrameSemantics} where

  open Core {FS}
  open Mach {FS}

  obs-correct-apply : ∀ {A B} → IRObsCorrectF (apply {A} {B})
  -- A PAIR fits no register and is not `Unit`, so the two off-pointer input
  -- residences are refuted outright.
  obs-correct-apply n l prog base _ cr span _ mIn x s alloc cl n≤ nh (in-reg () _) k
  obs-correct-apply n l prog base _ cr span _ mIn x s alloc cl n≤ nh (in-unit ()) k
  obs-correct-apply {A} {B} n l prog base _ cr span _ mIn x s alloc cl n≤ nh
    (in-loc pair-loc valid bf rdi) k =
    go (PairValidWF.fst-cell d) (PairValidWF.snd-cell d)
    where
      d = decomposePairWF valid
      module ASP = ApplySetupPres n prog base s alloc cl

      -- A CLOSURE is never inline (`InlineRep (A ⇛ B)` needs `FitsInRegI` or
      -- `≡ Unit`, both absurd), and D184 pins it to the HEAP — which is also
      -- the only shape `do-call` enters on, so the `AtStack` case is refuted
      -- by the witness's own `LocMatchesMode`.
      go : CellAt alloc (A IRTy.⇛ B) (proj₁ x) pair-loc s
         → CellAt alloc A (proj₂ x) (sucLoc pair-loc) s
         → MachineRefinesObsF prog base n l (apply {A} {B}) x s alloc cl k
      go (cell-inline (rep-prim ()) _) _
      go (cell-inline (rep-unit () _) _) _
      go (cell-ptr {comp-loc = AtStack _ _} _ _ fv) _ =
        ⊥-elim (ClosureValidWF.loc-mode (decomposeClosureWF fv))
      go (cell-ptr {comp-loc = AtDynamic chl} fst-cell fst-bf fst-valid) sc =
        assemble (ClosureValidWF.env-at cvw) sc
        where
          fst-loc = AtDynamic {FS} chl
          cvw     = decomposeClosureWF fst-valid

          E    = ClosureValidWF.EnvType cvw
          body = ClosureValidWF.body cvw
          env  = ClosureValidWF.env cvw
          blbl    = ClosureValidWF.body-label cvw

          -- Each residence contributes a STORED VALUE and the cell equation;
          -- the callee's cell is rebuilt from the same split (D187).
          env-sv-of : EnvAt alloc {E} env fst-loc s → StoredValue FS
          env-sv-of (env-at-loc el _ _ _) = SV-Ptr el
          env-sv-of (env-in-cell rep _)   = inline-sv rep env

          env-cell-of : (ea : EnvAt alloc {E} env fst-loc s)
                      → MemOps.readLoc s fst-loc ≡ just (env-sv-of ea)
          env-cell-of (env-at-loc _ ep _ _) = ep
          env-cell-of (env-in-cell _ ep)    = ep

          arg-sv-of : CellAt alloc A (proj₂ x) (sucLoc pair-loc) s → StoredValue FS
          arg-sv-of (cell-ptr {comp-loc = al} _ _ _) = SV-Ptr al
          arg-sv-of (cell-inline rep _)              = inline-sv rep (proj₂ x)

          arg-cell-of : (c : CellAt alloc A (proj₂ x) (sucLoc pair-loc) s)
                      → MemOps.readLoc s (sucLoc pair-loc) ≡ just (arg-sv-of c)
          arg-cell-of (cell-ptr ap _ _)  = ap
          arg-cell-of (cell-inline _ ap) = ap

          assemble : EnvAt alloc {E} env fst-loc s
                   → CellAt alloc A (proj₂ x) (sucLoc pair-loc) s
                   → MachineRefinesObsF prog base n l (apply {A} {B}) x s alloc cl k
          assemble ea sc' = record
            { value-realized =
                realized (17 + CalleeRun.steps crun) (CalleeRun.settle crun)
                         (CalleeRun.out-mode crun) (CalleeRun.cont-alloc crun)
                         run (CalleeRun.live crun)
                         (CalleeRun.returned crun) (CalleeRun.no-ret crun)
                         (CalleeRun.no-link crun) place (λ fr j bf → mem-pres-apply (AtStack fr j) bf) (λ hl bf → mem-pres-apply (AtDynamic hl) bf)
                         (trans (CalleeRun.frame-pres crun (falloc ASP.a16)
                                   (cong falloc call-eq))
                                OB.cf-a16)
                         bf-mono-apply
            ; traces-agree = trc
            }
            where
              module OB = ASP.Obligations pair-loc fst-loc (arg-sv-of sc') (env-sv-of ea)
                            rdi fst-cell (arg-cell-of sc') (env-cell-of ea) bf fst-bf n≤ nh

              callee-env : (ea' : EnvAt alloc {E} env fst-loc s)
                         → MemOps.readLoc (floc ASP.a16) (AtDynamic ASP.ahl)
                           ≡ just (env-sv-of ea')
                         → CellAt (falloc ASP.a16) E env (AtDynamic ASP.ahl) (floc ASP.a16)
              callee-env (env-at-loc el ep eb ev) q =
                cell-ptr q (OB.bf-advance eb) (OB.carry env el eb ev)
              callee-env (env-in-cell rep ep) q = cell-inline rep q

              callee-arg : (c : CellAt alloc A (proj₂ x) (sucLoc pair-loc) s)
                         → MemOps.readLoc (floc ASP.a16) (sucLoc (AtDynamic ASP.ahl))
                           ≡ just (arg-sv-of c)
                         → CellAt (falloc ASP.a16) A (proj₂ x)
                             (sucLoc (AtDynamic ASP.ahl)) (floc ASP.a16)
              callee-arg (cell-ptr ap abf av) q =
                cell-ptr q (OB.bf-advance abf) (OB.carry (proj₂ x) _ abf av)
              callee-arg (cell-inline rep ap) q = cell-inline rep q

              callee-in : InputAt {E IRTy.* A} Heap (falloc ASP.a16)
                            (env , proj₂ x) (floc ASP.a16)
              callee-in = in-loc (AtDynamic ASP.ahl)
                            (valid-pair-wf tt OB.before-ahl-suc
                              (callee-env ea OB.pair-fst-a16)
                              (callee-arg sc' OB.pair-snd-a16))
                            OB.before-ahl OB.input1-a16

              cinfo = BlockRuns.closures cr body env blbl
                        (subst (λ f → ValidAtWF _ alloc {A IRTy.⇛ B} f fst-loc s)
                               (ClosureValidWF.f-is-closure cvw) fst-valid)
                        (ClosureValidWF.code-ptr cvw)

              j      = proj₁ cinfo
              feq    = proj₁ (proj₂ cinfo)
              runner = proj₂ (proj₂ cinfo)

              -- THE CALL. `callView`'s three levels, spelled out from the
              -- three facts the setup and the witness already give.
              call-eq : flat-exec-instr instr-call-closure prog ASP.a16
                      ≡ record ASP.a16
                          { falloc = enter-call (falloc ASP.a16)
                          ; fret   = suc (fpc ASP.a16) ∷ fret ASP.a16
                          ; flink  = just (suc (fpc ASP.a16))
                          ; fpc    = j }
              call-eq =
                trans (cong (λ z → do-call-sv prog z ASP.a16)
                         (ASP.closure-reg pair-loc fst-loc (arg-sv-of sc') n≤ bf rdi
                            (arg-cell-of sc') fst-cell))
                (trans (cong (λ z → do-call-code prog z ASP.a16)
                         (ASP.code-cell fst-loc blbl n≤ OB.rdi12' OB.rdi14'
                            (ClosureValidWF.sucLoc-before cvw) (ClosureValidWF.code-ptr cvw)))
                       (cong (λ z → do-call-at z ASP.a16) feq))

              crun : CalleeRun prog (flat-exec-instr instr-call-closure prog ASP.a16)
                       (suc (fpc ASP.a16)) B (evalᴰ body (env , proj₂ x)) k
              crun = runner (flat-exec-instr instr-call-closure prog ASP.a16)
                       (falloc ASP.a16) (env , proj₂ x) (suc (fpc ASP.a16)) k Heap
                       (trans (cong fpc call-eq) refl)
                       (trans (cong (λ st → halted (floc st)) call-eq) OB.nh16)
                       (trans (cong fret call-eq) refl)
                       (trans (cong falloc call-eq) refl)
                       -- the call does not touch `floc`, but `do-call` is
                       -- stuck until `call-eq` says which branch it took.
                       (subst (λ st → InputAt {E IRTy.* A} Heap (falloc ASP.a16)
                                        (env , proj₂ x) st)
                              (sym (cong floc call-eq)) callee-in)

              run17 : FlatSteps prog 17 (entry-flat base s alloc cl)
                        (flat-exec-instr instr-call-closure prog ASP.a16)
              run17 = (OB.nh0 , span 0 _ refl) ∷ (OB.nh1 , span 1 _ refl)
                    ∷ (OB.nh2 , span 2 _ refl) ∷ (OB.nh3 , span 3 _ refl)
                    ∷ (OB.nh4 , span 4 _ refl) ∷ (OB.nh5 , span 5 _ refl)
                    ∷ (OB.nh6 , span 6 _ refl) ∷ (OB.nh7 , span 7 _ refl)
                    ∷ (OB.nh8 , span 8 _ refl) ∷ (OB.nh9 , span 9 _ refl)
                    ∷ (OB.nh10 , span 10 _ refl) ∷ (OB.nh11 , span 11 _ refl)
                    ∷ (OB.nh12 , span 12 _ refl) ∷ (OB.nh13 , span 13 _ refl)
                    ∷ (OB.nh14 , span 14 _ refl) ∷ (OB.nh15 , span 15 _ refl)
                    ∷ (OB.nh16 , span 16 _ refl) ∷ []

              run : FlatSteps prog (17 + CalleeRun.steps crun)
                      (entry-flat base s alloc cl) (CalleeRun.settle crun)
              run = FlatSteps-++ run17 (CalleeRun.run crun)

              -- D189 (repair): the callee's obligations are stated at
              -- `evalᴰ body (env , arg)`, the caller's at `evalᴰ apply x`
              -- (i.e. `proj₁ x (proj₂ x)`). Those agree by the closure
              -- record's OWN equation — `f-is-closure` — and that equation is
              -- propositional, so it is spent here rather than assumed to
              -- hold definitionally. It used to typecheck without this while
              -- `ValidAtWF` had exactly two constructors at `A ⇛ B`; adding
              -- `valid-ν-susp-wf` made `decomposeClosureWF` stop reducing far
              -- enough for the coincidence to survive. The decomposition
              -- hands over the equation for exactly this purpose.
              denot-eq : evalᴰ body (env , proj₂ x) ≡ evalᴰ (apply {A} {B}) x
              denot-eq = cong (λ g → g (proj₂ x))
                              (sym (ClosureValidWF.f-is-closure cvw))

              place : ResultPlace B (CalleeRun.out-mode crun)
                        (falloc (CalleeRun.settle crun)) (CalleeRun.cont-alloc crun)
                        (TM.valueT (evalᴰ (apply {A} {B}) x) k)
                        (floc (CalleeRun.settle crun))
              place = subst (λ d → ResultPlace B (CalleeRun.out-mode crun)
                                     (falloc (CalleeRun.settle crun))
                                     (CalleeRun.cont-alloc crun)
                                     (TM.valueT d k) (floc (CalleeRun.settle crun)))
                            denot-eq (CalleeRun.place crun)

              -- D204: what the whole `apply` leaves alone — the sixteen setup rows
              -- (`setup-mem-pres`, already proved) composed with the callee's
              -- own preservation. The callee's `pre` is `falloc a16`, NOT
              -- `alloc`: the setup allocates the `(env , arg)` pair, so the
              -- frontier has moved, and `bf-advance` is what carries the
              -- caller's `BeforeFrontier` across it.
              -- The setup ALLOCATES the callee's pair, so the frontier moves
              -- twice: `bf-advance` across the sixteen rows, then the callee's.
              bf-mono-apply : ∀ (m : ℕ) (loc : ValueLocation FS)
                            → BeforeFrontier (record alloc { next-slot = m }) loc
                            → BeforeFrontier
                                (record (falloc (CalleeRun.settle crun)) { next-slot = m }) loc
              bf-mono-apply m loc bf =
                CalleeRun.bf-mono crun (falloc ASP.a16) m (cong falloc call-eq) loc
                  (frontier-monotone (record alloc { next-slot = m })
                     (record (falloc ASP.a16) { next-slot = m })
                     (sym OB.cf-a16) ≤-refl OB.heapref-a16-≤ loc bf)

              mem-pres-apply : ∀ (loc : ValueLocation FS)
                             → BeforeFrontier (record alloc { next-slot = n }) loc
                             → MemOps.readLoc (floc (CalleeRun.settle crun)) loc
                               ≡ MemOps.readLoc s loc
              mem-pres-apply loc bf =
                -- The callee preserves the caller's frame at ANY bound; the
                -- setup's own preservation is at apply's frontier `n`. The
                -- lift across the setup keeps the bound and moves only the
                -- heap frontier (the setup allocates the callee's pair).
                trans (CalleeRun.mem-pres crun (falloc ASP.a16) n
                         (cong falloc call-eq) loc
                         (frontier-monotone (record alloc { next-slot = n })
                            (record (falloc ASP.a16) { next-slot = n })
                            (sym OB.cf-a16) ≤-refl OB.heapref-a16-≤ loc bf))
                      (trans (cong (λ st → MemOps.readLoc (floc st) loc) call-eq)
                             (ASP.setup-mem-pres n≤ OB.rdi12' OB.rdi14' loc bf))

              trc : take k (chain-events run) ≡ take k (projTrace (evalᴰ (apply {A} {B}) x) k)
              trc = trans (cong (take k) (chain-events-++ run17 (CalleeRun.run crun)))
                          (trans (CalleeRun.events crun)
                                 (cong (λ d → take k (projTrace d k)) denot-eq))

  ------------------------------------------------------------------------
  -- D199: `obs-correct-Out` — FORCING, DISCHARGED.
  --
  -- `obs-correct-apply`'s argument with the pair-packing removed. A suspension
  -- IS the callee record — cell 0 the argument, cell 1 the code — so the setup
  -- is three rows instead of sixteen, and it writes NO memory at all:
  -- `instr-save-closure-reg` moves a FlatState register, `load-indirect` and
  -- `mov-to-input` move machine registers. Neither touches the ALLOCATOR
  -- either, definitionally, so `apply`'s frontier-advance plumbing
  -- (`bf-advance`, the `next-slot`/`next-heap-ref` bounds) collapses here: the
  -- only transport left is across the state, and even that is by a memory map
  -- that is pointwise equal.
  --
  -- What the ν's witness supplies that a closure's does not is the SEED.
  -- `valid-ν-susp-wf` names the coalgebra and the seed the suspension was built
  -- from, so matching on it pins the input `x` to
  -- `valueT (evalᴰ (Ana wf coalg) seed) 0` — exactly the ν that `CoalgRuns` is
  -- conditioned on. That is why this clause needs no `denot-eq` step where
  -- `apply` spends `f-is-closure`: the block's claim and the goal are the same
  -- term, once the two functor witnesses are identified.
  ------------------------------------------------------------------------

