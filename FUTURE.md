# Future Tasks

## Standard Strata (Bundled Standard Library)

**Goal**: Bundle Strata with the compiler so users don't need `--strata` for standard imports.

**Current behavior**: Users must specify `--strata PATH` to resolve imports like `I.Linux.Syscalls`.

**Desired behavior**: Standard imports work out of the box, like GCC's libc or Rust's std.

### Approach

1. **Bundle Strata with compiler binary**
   - Use `data-files` in cabal to include `Strata/` with the executable
   - Look for Strata relative to the compiler binary path

2. **Search order** (like GCC include paths):
   ```
   1. Explicit --strata flag (override)
   2. Strata/ relative to input file (project-local)
   3. ~/.once/strata/ (user install)
   4. /usr/share/once/strata/ (system install)
   5. Bundled with compiler binary (fallback)
   ```

3. **Error handling**:
   - If no `--strata` and no imports need resolution → just work
   - If import can't be resolved → clear error with search paths tried

### Implementation Notes

- Use `Paths_once` module from cabal to find data directory
- Consider separate "standard" vs "extended" Strata modules
- Keep `-I:TYPE MODULE` for explicit override cases
