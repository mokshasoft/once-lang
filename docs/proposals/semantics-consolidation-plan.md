# Semantics Module Consolidation Plan

**Date:** 2026-03-18
**Status:** Draft - To be implemented

---

## Problem Statement

The current semantics modules have overlapping concerns and poor naming:

| Module | What it contains | Issues |
|--------|------------------|--------|
| `Once.Sem` | Pure type interpretation, plain functions | Good but poorly named |
| `Once.SemanticBase` | Closure record, encoding postulates | Conflates semantics with memory layout |
| `Once.Semantics` | IR eval using SemanticBase | Inherits encoding baggage |
| `Once.CCC.Eval` | Parameterized IR eval | Good pattern, duplicates functionality |

### Key Issues

1. **`env-addr : Word` in Closure is not semantics** - it's a compilation detail
2. **Encoding postulates are not portable** - they assume specific memory representation
3. **`evalPrim` as postulate vs parameter** - `Once.CCC.Eval` does it right, `SemanticBase` doesn't
4. **Naming confusion** - `Once.Semantics` suggests THE semantics, but it's encoding-specific
5. **Duplication** - Two `⟦_⟧` definitions, two eval functions

---

## Target Architecture

```
Once.Semantics (THE portable denotational semantics)
├── ⟦_⟧ : Type → Set
│   └── Functions = plain Agda functions (⟦ A ⇒ B ⟧ = ⟦ A ⟧ → ⟦ B ⟧)
├── ⟦Fix⟧ wrapper
├── sem-* operations (sem-fst, sem-snd, sem-pair, sem-inl, sem-inr, sem-case, sem-fold, sem-unfold)
├── Semantic laws (sem-fst-pair, sem-case-inl, etc.)
├── PrimSem record (parameterized primitive semantics)
├── eval : PrimSem → IR A B → ⟦ A ⟧ → ⟦ B ⟧
└── NO POSTULATES, NO MEMORY MODEL

Once.Backend.Encoding (memory representation for backends)
├── Closure record with env-addr : Word
├── ⟦_⟧ₑ : Type → Set (encoding-aware interpretation)
├── encode : ⟦ A ⟧ₑ → Word
├── encode-* postulates (justified by backend implementation)
└── Used ONLY by backend proofs that need memory layout
```

---

## Migration Steps

### Phase 1: Consolidate Pure Semantics

**Goal:** Make `Once.Semantics` the single source of truth for portable denotational semantics.

1. **Rename `Once.Sem` → content goes into `Once.Semantics`**
   - Keep `⟦_⟧` with plain functions
   - Keep `⟦Fix⟧`, `wrap`, `unwrap`
   - Keep all `sem-*` operations
   - Keep semantic laws

2. **Move `PrimSem` and `eval` from `Once.CCC.Eval` → `Once.Semantics`**
   - The parameterized approach is correct
   - Delete `Once.CCC.Eval` after migration

3. **Update all imports**
   - Modules using `Once.Sem` → use `Once.Semantics`
   - Modules using `Once.CCC.Eval` → use `Once.Semantics`

**Files to modify:**
- `Once/Semantics.agda` - rewrite with pure content
- `Once/CCC/Eval.agda` - delete (merged into Semantics)
- `Once/Sem.agda` - delete (merged into Semantics)
- All files importing these modules

### Phase 2: Isolate Encoding Concerns

**Goal:** Move memory-specific stuff to a backend module.

1. **Create `Once.Backend.Encoding`** (or `Once.CCC.Encoding`)
   - Move `Closure` record with `env-addr`
   - Move `⟦_⟧` that uses `Closure` (rename to `⟦_⟧ₑ` for clarity)
   - Move all `encode-*` postulates
   - Move `encode` function
   - Document that this is backend-specific, not portable

2. **Rename `Once.SemanticBase` → delete or merge into Encoding**
   - All its content goes to `Once.Backend.Encoding`

3. **Update backend proofs**
   - `Once.CCC.Target.X86v3.*` modules that need encoding
   - Import from `Once.Backend.Encoding` instead of `SemanticBase`

**Files to modify:**
- `Once/SemanticBase.agda` - delete (content to Encoding)
- `Once/Backend/Encoding.agda` - create new
- `Once/CCC/Target/X86v3/Dispatcher/*.agda` - update imports
- Other backend files using Closure/encoding

### Phase 3: Clean Up Dependencies

**Goal:** Ensure clean separation between portable and backend-specific.

1. **Audit imports**
   - `Once.Semantics` should NOT import any backend modules
   - `Once.Backend.Encoding` can import `Once.Semantics` (not vice versa)
   - Frontend proofs (Optimize, Escape, Fusion) use only `Once.Semantics`
   - Backend proofs can use both

2. **Remove `Closure-η` postulate if possible**
   - Check if it's actually needed
   - If needed, move to `Once.Backend.Encoding`

3. **Verify build**
   - `make compiler` must pass
   - All proofs must still type-check

---

## File Changes Summary

### Delete
- `Once/Sem.agda` (merged into Semantics)
- `Once/SemanticBase.agda` (merged into Backend.Encoding)
- `Once/CCC/Eval.agda` (merged into Semantics)

### Create
- `Once/Backend/Encoding.agda` (memory representation)

### Major Rewrite
- `Once/Semantics.agda` (becomes THE portable semantics)

### Update Imports (many files)
- `Once/Category/Laws.agda`
- `Once/Optimize.agda`, `Once/Optimize/Correct.agda`
- `Once/Escape.agda`, `Once/Escape/Correct.agda`
- `Once/Fusion.agda`, `Once/Fusion/Correct.agda`
- `Once/Surface/*.agda`
- `Once/CCC/Target/X86v3/**/*.agda`
- Others as needed

---

## Resulting Module Structure

```
Once/
├── Type.agda                    # Types (unchanged)
├── Semantics.agda               # THE portable semantics (consolidated)
│   ├── ⟦_⟧ (plain functions)
│   ├── sem-* operations
│   ├── PrimSem record
│   └── eval (parameterized)
├── CCC/
│   ├── IR.agda                  # THE IR (unchanged)
│   └── ...
├── Backend/
│   └── Encoding.agda            # Memory representation (new)
│       ├── Closure with env-addr
│       ├── ⟦_⟧ₑ (encoding-aware)
│       ├── encode-* postulates
│       └── encode function
└── ...
```

---

## Verification Checklist

- [ ] `Once.Semantics` has no postulates
- [ ] `Once.Semantics` does not import memory/encoding modules
- [ ] `eval` is parameterized by `PrimSem` (not postulated)
- [ ] All frontend proofs use `Once.Semantics`
- [ ] Backend proofs use `Once.Backend.Encoding` where needed
- [ ] `make compiler` passes
- [ ] No duplicate `⟦_⟧` definitions (one in Semantics, one in Encoding)

---

## Open Questions

1. **Naming:** `Once.Backend.Encoding` vs `Once.CCC.Encoding` vs `Once.Memory.Encoding`?
   - Suggestion: `Once.Backend.Encoding` makes the backend-specific nature clear

2. **SemanticsS (sized):** There's also `Once.SemanticsS` - does it need similar treatment?
   - Check if it's still used and whether it has the same issues

3. **Closure representation:** Do any frontend proofs actually need `Closure` with `env-addr`?
   - If not, the split is clean
   - If yes, we need to reconsider

4. **Int representation:** `Once.Sem` uses `ℕ` for Int, `Once.SemanticBase` uses `ℤ`
   - Need to decide which is correct and unify

---

## Estimated Effort

- Phase 1 (Consolidate Pure Semantics): ~2 hours
- Phase 2 (Isolate Encoding): ~2 hours
- Phase 3 (Clean Up): ~1 hour
- Testing and fixing: ~1 hour

Total: ~6 hours

---

## Notes

This consolidation aligns with the broader goal of OCP-0003 (Prim/Poly layered IR) by establishing a clean, portable semantic foundation that doesn't conflate compilation concerns with mathematical semantics.
