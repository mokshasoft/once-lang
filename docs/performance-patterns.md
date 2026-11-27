# Performance patterns: checking the proofs, running the compiler

What made things slow before, and what fixed it. Apply these first; profile or bisect only when
none of them explains a slowdown. Every slowdown found is recorded here.

The caps (each unit of work, never the run as a whole):

| Unit | Cap | Enforced by |
|---|---|---|
| an Agda module | 60 s, 3 GB | `formal/scripts/watchdog.sh` in the Makefile's `AGDA_CMD` (`AGDA_UNIT_SECS`), `agda-safe.sh` (memory), `agda-keepgoing.py --kill` |
| a GHC module of the compiler (nix, one core) | `SEL4_UNIT_SECS` (600 s) of silence | `watchdog.sh` around `nix build -L` in `tests/run-sel4-tests.sh` |
| a test program's compile | 5 s (`ONCE_BUILD_TIMEOUT`) | `tests/run-exit-tests*.sh` |
| a test program's run | 10 s | the same scripts |
| a seL4 image's compile | 5 s | `timeout` in `examples/seL4/flake.nix` (`mkImage`) |

Master compiles every exit test in at most 0.1 s and every seL4 image in at most 0.9 s. A unit over
its cap is a failure to report and fix, never a run to wait out.

## A. Checking time (Agda)

1. **No `with`, no `rewrite`.** A `with` makes an auxiliary function abstracted over the whole
   clause context, rechecked with it; in a definition that proofs reduce it also hides the
   scrutinee. Use a named top-level helper taking the scrutinee's value (`Dec`, `Maybe`, `⊎`).
2. **Lift `where` proofs to top-level `private` lemmas** with their own explicit arguments. A
   `where` block is checked under the whole clause context.
3. **Conversion normalises both sides fully when they are not syntactically equal.** Seal terms
   that occur in types and are computed (`opaque` plus a `-def` unfolding lemma): image prefix
   lengths (`pos`), label names (`nameOf`), evidence (`blocks-in`). Move between spellings with
   `subst` over variables, never by conversion of computed terms.
4. **Give every argument a meta would be solved by unfolding.** `_` arguments, `→ _`
   continuation results, `subst` motives through defined type families: write the term, or a
   local `Goal = …` and `→ Goal`.
5. **Split a big indexed family once**, in a small module, as an eliminator whose cases come in
   one record argument; give explicit absurd clauses; put `∀ {implicits}` after the view
   argument, since implicits split first.
6. **Constructor copies per module application**: `open import M args` in two modules gives
   two copies of each constructor, compared by unfolding. Call lemmas generic over the key
   with the caller's own key.
7. **Pattern lambdas in a big mutual block** become functions in the termination graph: use an
   irrefutable `let (a , b) = e in …` for single-clause record matches.
8. **Inline `[ f , g ]′ (∈-++⁻ …)` in a proof that occurs in types** is walked at each
   comparison: seal it (`opaque`) or use a named helper. D493 (2026-11-26): `Keys.rg-cl`,
   `own-got` and `RunOps.ok-own` (evidence with `∈-++⁻` splits, inside the universe and the
   key evidence) took `LinCore.Apex` from 33 s to 117 s; sealing the owned entry (`ownω`) and
   the lemma taking them was not enough, as their arguments are still compared. Sealed: 43 s.
9. **Interface load**: importing a large walk (the front end) into an apex module can exceed
   the memory cap on import alone; take its facts as a record premise instead.
10. **Large literals in proofs: make the constant `opaque`.** A literal used as the
    *first* argument of a non-builtin-reducing function (`(32768 + b) * 4`: `_*_` recurses on
    its first argument) unfolds one `suc` at a time in conversion. D488's
    `start-stack-words` took x86-32's `FlatSimulation` past the 2.7 GB heap until it was
    sealed; after, 23 s. Proofs need no constant's value; extraction still sees it.
11. **Bisect with probe modules**: copy the module header, `head -N` of the body, `?` bodies
    (they still give timings), `--profile=definitions` (`--profile=internal` when
    "Miscellaneous" is large), `/usr/bin/time -f %M` for memory.

## B. Run time of the extracted compiler (MAlonzo)

The compiler is the Agda definitions run by GHC. Nothing about them is free because it is a
proof.

1. **Nothing in a parameterised module is shared.** A definition under module parameters
   (`Lowering U …`) compiles to a function of those parameters, recomputed at every call:
   a list derived from the universe (`allK U`, a liveness table) costs its whole computation
   per use. Compute it once: a field of the record the module takes (fields are thunks,
   evaluated once), or an argument the caller binds once.
2. **Proofs are run-time data unless erased.** Membership proofs, evidence records (`BIn`,
   `CIn`) and their positions (`idx p`: a walk down the proof) are built and walked at run
   time. A position recomputed per use from a long `∈-++⁺ʳ …` chain costs the list's length
   each time. Erase what is only a proof (`@0`, `Prop`, irrelevance) and carry positions as
   numbers where the code needs them.
3. **Well-founded recursion is slow.** `Acc` is ordinary data: `charsInBase`, `showInBase` and
   anything over `<-wellFounded` build accessibility proofs as they go. Use structural
   recursion (fuel) in code the compiler runs often (label names).
4. **Lists without deduplication grow with the program.** One entry per occurrence (types per
   use, closures per site) makes every later pass over the list, and every search in it, scale
   with program size, and emits duplicate code (the seL4 Words image: 1,394 blocks, 290
   distinct, 69% of its lines duplicates). Deduplicate where the list is made, ONCE (D487,
   `Keys.closeD`, `TyEq.eqT`), and find an element's place by searching the deduplicated list
   (`Keys.find`), its existence a lazy witness never computed. A membership built THROUGH the
   deduplication (`∈-deduplicate⁺`) is computed at run time: that was slower than no
   deduplication at all.
5. **Repeated search instead of a map.** `any (j ≡ᵇ_) xs` per element is quadratic; build the
   lookup once (pattern 1) or decide from the element itself. Evidence per element: build it
   for all elements in one pass (`All P xs`, `Keys.tm-all`) and look it up, rather than
   deriving it from a membership proof each time (`tm-good`, which rebuilt every enclosing
   subterm's key list per lookup).
6. **`with` and nested pattern lambdas blow up the generated case trees** (same cure as A1).
7. **Strict string appends.** `String` is strict text: `a ++ b` copies both. Text built as
   `line ++ rest` copies the rest at every line, quadratic in the output (65% of a large
   image's compile). Build the pieces as a list and join once (`Once.Target.Text.join`).
8. **Laziness is the friend.** A value the compiler never inspects is never computed: a
   witness used only in an impossible branch, a proof under a constructor nobody matches.
   Shape code so the run-time path reads small data and the proofs ride along unevaluated.

**Finding the cost.** `+RTS -s` (allocation vs residency: high allocation with low residency
means recomputation), then `perf record` on the optimised binary (GHC's symbols name each
top-level function: `…_du_idx_…`, `…_du_ts_…`, `__memmove…`). The profiling build
(`--enable-profiling`) panics GHC at `-O` and crashes at run time at `-O0` on MAlonzo code.

**Compile time, 2026-11-24** (x86_64, the same inputs): master compiles every exit test in at
most 0.10 s (all 108: 6.6 s) and every seL4 image in at most 0.89 s; the branch after D487,
0.13 s (6.7 s) and 1.18 s (at most 1.9× master per image). Before D487 an seL4 image took over
60 s (Words, Caps) — B1, B2, B4 and B7 together.

## C. Measuring

- `tests/perf-compare.sh` measures run time and code size against master; compile time is
  measured per program in the same way (master's are the reference above).
- Every test runner prints minutes per stage; compare with the previous run while waiting.
