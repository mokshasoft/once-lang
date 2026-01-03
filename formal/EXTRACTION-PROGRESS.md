# RISC-V Modular Extraction Progress
**Date:** 2026-01-03
**Status:** 5/14 IR cases extracted, MutualIR still times out (1736-line mutual block)

## ✅ Completed & Committed (4669829)

**Extracted IR Base Case Modules** - All type-check successfully:
- Id.agda, Terminal.agda, Fold.agda, Unfold.agda, Arr.agda
- Each ~50 lines with stateful wrapper (`run-*-star-s`)
- Bridge postulate `irresults-preserves-eval` added to MutualIR.agda

## 🚧 Remaining Work

**Mutual Block:** Lines 229-1965 (1736 lines) - still times out

**To Extract:**
- Simple: fst, snd, initial (one-liners)
- Medium: curry, apply (use proven runners)
- Complex: compose (~65 lines + helpers), pair (+ helpers), case (~large + helpers)

## 🎯 Next Step

Extract compose case + helpers to Compose.agda, type-check, commit. Repeat for pair and case.
Then update MutualIR to call extracted modules instead of inline implementations.
