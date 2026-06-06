# Minimal CCC-VM: Glue and Op Set (Sketch)

Companion to [tcb0-inspectable-vm.md](./tcb0-inspectable-vm.md).

**Key simplification:** make the VM an **evaluator** (compute a closed term to a
canonical value), not a term-rewriter. The fixpoint check then reduces to
value-equality, and all syntax-normalization machinery disappears from the TCB.

## 1. Values — 6 heap cell kinds

```
Value ::= UNIT | PAIR a b | INL a | INR a | IN a | CLO code env
```

`CLO` holds a term-pointer + captured env-value (for `curry`/`apply`).
Cells come from a bump arena.

## 2. Program = data — 14 read-only term tags

```
ID  COMP f g  FST  SND  PAIR f g  INL  INR  CASE f g
CURRY f  APPLY  TERM  IN  OUT  CATA f F
```

Leaves carry nothing; `COMP/PAIR/CASE` carry two sub-pointers; `CURRY/CATA` one.
`CATA` also carries a **functor descriptor** `F` (see §6).

## 3. Three primitive moves (the shared vocabulary)

```
LOAD field      -- read a cell field          (projection, untag)
ALLOC tag …     -- allocate a tagged cell     (pairing, injection, closure, In)
TAGTEST         -- branch on a cell's tag     (case, apply destructure)
```

Every op below is a thin use of these three — "one place each" is literal: the
three primitives live in one place, the ops just call them.

## 4. Op set = the dispatcher (backed, law-checkable code)

`eval(t, R) → R'`, switching on `t.tag`. Each line *is* the categorical law:

```
ID     → R
COMP   → eval(t.f, eval(t.g, R))            -- (f∘g)(x)=f(g(x))
FST    → LOAD R.a        SND → LOAD R.b
PAIR   → ALLOC PAIR (eval(t.f,R)) (eval(t.g,R))
INL    → ALLOC INL R     INR → ALLOC INR R
CASE   → TAGTEST R:  INL x→eval(t.f,x) | INR y→eval(t.g,y)
TERM   → UNIT
CURRY  → ALLOC CLO t.f R                          -- capture env
APPLY  → eval(R.a.code, ALLOC PAIR R.a.env R.b)   -- R = (clo,arg)
IN     → ALLOC IN R      OUT → LOAD R.a
CATA   → eval(t.f, fmap(λx.eval(t,x), t.F, R.a))  -- R = IN w
```

14 entries, each 1–3 primitive moves. This table is what the human auditor checks
against category theory, op by op.

## 5. Glue inventory (unbacked code — minimize this)

| Glue            | Size                  | Note                                                       |
|-----------------|-----------------------|------------------------------------------------------------|
| Dispatcher      | the `switch` skeleton | closed control flow                                        |
| Control stack   | 1 explicit stack      | de-recursify `COMP`/`PAIR`/`CATA`; bounded, no call stack  |
| Bump allocator  | ~3 lines              | bounds-checked — the memory-safety leg                     |
| `fmap` helper   | §6                    | the only nontrivial glue                                   |
| Structural `equal` | 1 tree walk        | for the fixpoint comparison                                |
| Parser          | 1 linear pass         | bytes → read-only term array                               |
| I/O             | 2 syscalls            | `read` input, `write` result                               |

## 6. The one hard piece: `cata`/`fmap`

`fmap` is generic, driven by the term's functor descriptor `F` (4 tags), so the
VM stays signature-agnostic:

```
fmap(g, REC,        x)      = g x
fmap(g, CONST,      x)      = x
fmap(g, PROD F1 F2, (x,y))  = (fmap(g,F1,x), fmap(g,F2,y))
fmap(g, SUM  F1 F2, INL x)  = INL (fmap(g,F1,x))    -- INR symmetric
```

~5 cases. All of `cata`'s complexity lives here, and it is still auditable.

## 7. The fixpoint check

```
v1 = eval(⌜N⌝,      UNIT)
v2 = eval(N ∘ ⌜N⌝,  UNIT)
output  equal(v1, v2)        -- VERIFIED / REJECTED
```

Because the VM evaluates to canonical values, you never rewrite syntax — you
compare two value trees.

## Size summary

- **Backed (law-checked):** 3 primitives + 14 one-line ops.
- **Unbacked (glue):** dispatcher + 1 control stack + bump allocator + 5-case
  `fmap` + tree-`equal` + parser + 2 syscalls.
- **6 value cells, 14 term tags, 4 functor tags.**

Plausibly a few hundred instructions — small enough for the four-point byte audit
(closure / faithfulness / isolation / memory-safety), and it maps almost 1:1 onto
a future C3PU instruction set.
