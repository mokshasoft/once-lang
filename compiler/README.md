# Once Compiler

Haskell implementation of the Once compiler.

## Building

```bash
cabal build
```

## Testing

```bash
cabal test
```

Also available via `make build` / `make test` (cabal-based).

> **Note on build tooling**: this project uses `cabal` directly, not
> `stack`. Stack 3.7.1 under Nix enters a self-referential loop in its
> GHC version resolution (`<<loop>>`) before any user code runs. The
> `once.cabal` file is authoritative; the nix flake's `once` package
> uses `callCabal2nix` against it. `stack.yaml` is retained for
> reference only.

## Documentation

- [Implementation Plan](../docs/compiler/implementation-plan.md) - Phased build plan
- [Decision Log](../docs/compiler/decision-log.md) - Design decisions and rationale

## Project Structure

```
src/Once/
├── Quantity.hs   # QTT quantities (Zero, One, Omega)
├── Type.hs       # Type representation
├── IR.hs         # Intermediate representation (12 generators)
├── Value.hs      # Runtime values for interpreter
├── Eval.hs       # IR interpreter
├── Syntax.hs     # Surface syntax AST
└── Parser.hs     # Megaparsec parser

test/
├── QuantitySpec.hs  # Semiring law tests
├── IRSpec.hs        # Categorical law tests
└── ParserSpec.hs    # Parser tests
```
