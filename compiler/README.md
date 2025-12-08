# Once Compiler

Haskell implementation of the Once compiler.

## Building

```bash
stack build
```

## Testing

```bash
stack test
```

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
