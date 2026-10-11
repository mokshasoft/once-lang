# Silent-gap classes

A catalogue of ways a proof can be valid while the model is silently too weak. It was
written for plan 0.9 (exhaustive semantics, D049), which closed one class: catch-all
absorption in semantic pattern matches. The plan is closed and deleted. The classes below
are kept as a checklist for reviews and audits (MERGE.md §1). The examples are from
2026-04 and may name modules that have since been removed.

### Gap class A: `⊤`-valued predicates pretending to constrain

Example:
```agda
WellFormed : T → Set
WellFormed _ = ⊤
```
Looks like a proof obligation; inhabited trivially. Any downstream
proof that asks for `WellFormed x` gets vacuous evidence.

**What closing it buys:** every predicate-valued name means
something; no cosmetic proof obligations. Callers relying on the
predicate can trust they're paying for real work.

**Mechanism candidates:** lint rule "predicate body must not
reduce to `⊤`"; reflection-based audit that rejects
`data P where triv : P` single-constructor predicates; review
discipline enforced by a named audit query.

### Gap class B: under-modeled abstract state

Example: `X86State` has no field for `r9`, so even an explicit
clause for `lea r9 …` is forced to be identity — there's nowhere
to write the value. The lea-offset bug had *both* this (no r9
field) AND a catch-all (no explicit clause). Closing just 0.9
would have forced an identity clause here; closing B would have
flagged the missing field but still allowed a catch-all to absorb
it.

**What closing it buys:** you can't claim to model an instruction
without also tracking the entities it affects. The abstract
machine's state type is complete with respect to the instruction
set it claims to simulate.

**Mechanism candidates:** for each architectural entity used in
codegen (every `Reg`, every `Mem` variant, every syscall-relevant
memory region), assert the state record has a field for it. A
reflection-based check that enumerates constructors of `Reg` and
verifies each has a read/write helper.

### Gap class C: `refl` proofs that only prove shape

Example:
```agda
theorem : f a ≡ f b
theorem = cong f (lemma a b)
```
If `f` reduces both sides to the same trivial form (e.g.
`f = const tt`), the theorem is true regardless of `lemma`. The
proof is valid; the statement is tautological.

**What closing it buys:** theorems say something. A proof's
normal form uses the variables the theorem's statement quantifies
over.

**Mechanism candidates:** hard to mechanize fully. Reflection-
based check "normalize the proof term; does it mention the
parameters the theorem quantifies over?" Alternatively: review
discipline for theorem statements.

### Gap class D: partial-result defaults (`Maybe`/`Sum`)

Example:
```agda
compile-result name with lookup name table
... | just v  = real-compilation v
... | nothing = trivial-default
```
Analogous to catch-all but on `Maybe`. `nothing` is treated as
"reasonable fallback" rather than "prove this can't happen."

**What closing it buys:** every partial-result branch discharges
a proof of absurdity, raises a typed error, or is an explicitly
named postulate. No trivia silently swallows real failure modes.

**Mechanism candidates:** grep-based lint — flag `... | nothing =
<non-⊥>` in specific function families; wrapper type
`Total : Maybe A → Set` that requires proof `just` always
results; review discipline backed by greppable audit.

### Gap class E: laundered / nested postulates

Example:
```agda
big-theorem : P
big-theorem = … where
  lemma : Q
  lemma = some-postulate      ← local, may escape top-level audit
```
Postulates inside `where`, `private`, or anonymous modules may
not surface in `make postulates` depending on how the grep is
written.

**What closing it buys:** the finite postulate audit surface is
truly finite — no hidden axioms in `where` blocks.

**Mechanism candidates:** strengthen `make postulates-grep` to
recurse into nested definitions; policy "all postulates at top
level, named, with justification comment"; reflection-based check
that enumerates every `postulate` declaration regardless of
nesting.

### Gap class F: specification drift via rename

Example: `foo : T → State` is renamed to `foo-v2` and semantically
reworked. Re-export from the old name still points at a stub or
at the new function with subtly different behavior. Proofs that
depended on `foo`'s old behavior may now be vacuous or wrong.

**What closing it buys:** a rename is either a true alias (same
semantics) or a break (new semantics, old name dropped). No
"gradual migration" via subtly-different same-named symbols.

**Mechanism candidates:** git-aware audit "this symbol's callers
have not been re-reviewed since its body changed"; reviewer
discipline; stronger naming discipline (version suffixes).
Hard to fully mechanize.

### Gap class G: hard-coded constants unchecked by the model

Example: the lea-offset bug itself. `lea r9 (rip+disp 4)` has a
literal `4` representing byte-arithmetic that the abstract
machine doesn't perform. Even with exhaustive case-splits (0.9)
and full state representation (B), if the semantics doesn't
*compute* RIP-relative addresses, the constant is unconstrained.

**What closing it buys:** concrete constants in emitted code are
derived by the compiler (or checked by the model), not written
by hand. No free parameters that readers must verify against
instruction-byte tables.

**Mechanism candidates:** model RIP-relative arithmetic in the
abstract semantics (high cost); derive the constant from a
length-computation function (`length setup-instrs` rather than
`4`); Sail-style ISA integration (large).

### Gap class H: trivial termination arguments

Example: a `step : T → T` function that only reduces cases
already in normal form. Trivially terminating; proofs about it
terminate but don't imply anything about reduction of
non-normal terms.

**What closing it buys:** termination proofs imply the claimed
computational behavior, not just "this function happens to
return on its trivial inputs."

**Mechanism candidates:** audit termination witnesses for "does
this function recurse non-trivially on the inputs it claims to
handle?"; wrapper type that demands evidence of progress.

### Summary

| Gap class | Mechanism | What it closes | Status |
|---|---|---|---|
| Catch-all in semantic pattern | **`--exact-split` + `CATCHALL`** | functions silently absorbing unmodeled constructors | **0.9 (this plan)** |
| A — `⊤`-predicates | predicate-body audit | vacuous proof obligations masquerading as real ones | future plan |
| B — under-modeled state | state-field coverage | instructions that change register X when X isn't in the state | future plan |
| C — `refl` on trivia | proof-normal-form audit | theorems vacuously true because both sides trivialize | future plan (hard) |
| D — `Maybe` defaults | `nothing`-branch discipline + lint | partial lookups pretending to be total | future plan |
| E — laundered postulates | strengthen postulate grep | postulates escaping audit via `where` / `private` | small follow-on |
| F — rename drift | git-aware audit | subtly-renamed symbols with unaudited reverse deps | future plan (hard) |
| G — hard-coded constants | model derivation or Sail-ISA | hand-written constants the model doesn't verify | future plan (large) |
| H — trivial termination | termination-witness audit | termination proofs that don't imply computational progress | future plan |

Each row is an independent audit surface. Closing any one is
independent of the others. Closing all of them is the full story
of "model faithfulness as a mechanical invariant." 0.9 is a
surgical first step: close the row that hid the lea-offset bug,
and leave the catalogue visible for whoever tackles the next row.

