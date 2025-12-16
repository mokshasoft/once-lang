# X86 Backend Full Proof Architecture

This document describes the architecture for achieving **complete proofs** for all 14 IR generators in the X86 backend with no postulates except encoding axioms.

## The Core Problem: Apply Cannot Be Proven in Isolation

The `apply` generator presents a fundamental proof challenge:

```
compile-x86 apply generates:
  mov r15, [rdi]      ; load closure
  mov rsi, [rdi+8]    ; load argument
  mov r12, [r15]      ; load env
  mov r15, [r15+8]    ; load code_ptr
  mov rdi, rsi        ; prepare arg
  call r15            ; JUMPS TO THUNK CODE (not in this program!)
```

After `call r15`, execution transfers to thunk code created by `curry`. When proving `apply` in isolation, that thunk code doesn't exist in the program being proven.

**This is fundamental to closure semantics, not a proof limitation.** Unlike other generators where execution stays within the compiled code, `apply` transfers control to external code (the closure's thunk).

## The Solution: Thunk Context

Instead of proving apply in isolation, we prove it works **given the thunk code exists in the program**:

```agda
run-apply-with-thunk : forall {A B C} (f : IR (A * B) C) (env : A) (arg : B)
  (thunk-offset : Nat) (prog : Program) (s : State) ->
  -- Precondition: thunk code exists at thunk-offset in prog
  prog-contains-thunk-at thunk-offset (compile-thunk f) ->
  -- Precondition: closure's code-ptr points to thunk-offset
  closure-code-ptr-eq s thunk-offset ->
  -- Standard preconditions
  halted s == false -> ... ->
  -- Result: apply produces correct output
  Exists s' (exec n prog s == just s' * rax s' == encode (eval f (env , arg)))
```

### Key Predicates

1. **`prog-contains-thunk-at`**: Asserts that the program contains valid thunk code at a specific offset
2. **`closure-code-ptr-eq`**: Asserts that the closure's code-ptr field points to the thunk offset

### Curry Creates Valid Closures

The `curry` generator must prove it creates closures with valid code-ptrs:

```agda
run-curry-creates-valid-closure : forall {A B C} (f : IR (A * B) C) (a : A) (s : State) ->
  ... ->
  Exists s' (run (compile-x86 (curry f)) s == just s'
         * closure-env s' == encode a
         * closure-code-ptr s' == thunk-entry-offset)  -- Points to embedded thunk
```

The RIP-relative `lea` instruction in the codegen computes the absolute address of the thunk code embedded in the curry instruction sequence.

## Composition Theorems

The real correctness statement: when curry and apply are in the same program:

```agda
run-curry-apply-correct : forall {A B C} (f : IR (A * B) C) (a : A) (b : B) ->
  Exists s (run (compile-x86 (apply . <curry f , id>)) (initWithInput (a , b)) == just s
        * rax s == encode (eval f (a , b)))
```

### Why This Works

In any well-typed Once program, every `apply` has a corresponding `curry` that created the closure. The categorical semantics guarantees this pairing. By proving them together (with thunk code in the same program), we achieve full proofs while respecting the language's structure.

### Generalization

The composition extends to `apply . <curry f , g>` for any `g`:
- First, `g` produces the argument value
- Then, `curry f` creates the closure
- The pair is formed and passed to `apply`
- `apply` calls the thunk with the argument, producing `eval f (env, arg)`

## Stack Invariants via WellFormed Predicate

To eliminate addr-diff postulates mechanically, we track stack state:

```agda
record WellFormed (s : State) : Set where
  field
    rsp-above-r15 : readReg (regs s) rsp > readReg (regs s) r15 || r15 == 0
    stack-separated : forall (n : Nat) -> n < 64 -> rsp - n != r15
```

### How It Eliminates Postulates

The addr-diff postulates assert that memory addresses computed from rsp don't collide with addresses stored in r15:
- `addr-diff-1`: `rsp != r15`
- `addr-diff-2`: `rsp + 8 != r15`

With a `WellFormed` invariant:
1. `initWithInput` creates a well-formed state (rsp high, r15 = 0)
2. Simple operations (id, fst, snd, terminal) preserve well-formedness
3. Stack operations maintain separation (sub rsp, 16 increases separation)
4. addr-diff lemmas follow directly from the invariant

## Frame Pointer Strategy for Stack Restoration

The `pair` codegen uses frame pointer (rbp) for reliable stack restoration:

```
compile-x86 <f , g> =
  push r14 ; push r15 ; push rbp    -- Save callee-saved
  mov rbp, rsp                       -- Save stack frame
  sub rsp, 16                        -- Allocate pair
  mov r15, rsp                       -- r15 = pair base
  mov r14, rdi                       -- r14 = saved input
  compile-x86 f
  mov [r15], rax                     -- Store f result
  mov rdi, r14                       -- Restore input
  compile-x86 g
  mov [r15+8], rax                   -- Store g result
  mov rax, r15                       -- Return pair pointer
  mov rsp, rbp                       -- RESTORE STACK (key!)
  pop rbp ; pop r15 ; pop r14        -- Restore registers
```

### Why Frame Pointer Works

Even if `f` or `g` allocate additional stack space (e.g., `curry` creates closures), the `mov rsp, rbp` instruction restores the stack to its state after the initial push sequence. This eliminates the need to track stack changes through recursive compilation.

### What It Replaces

The `rsp-eq-r15-after-g` postulate assumed that rsp equals r15 after executing g, which isn't true when g allocates stack. The frame pointer approach:
- Captures the restoration point in rbp
- Restores correctly regardless of f/g stack usage
- Is already implemented in the codegen

## Implications for Other Backends

This architecture applies to AArch64 and RISC-V as well:

| Backend | Branch to Thunk | Link Register | Frame Pointer |
|---------|-----------------|---------------|---------------|
| x86-64  | `call r15`      | (on stack)    | rbp           |
| AArch64 | `blr x9`        | x30           | x29           |
| RISC-V  | `jalr x15`      | ra            | s0            |

The same proof structure works:
1. Define `ThunkSpec` for the backend
2. Prove curry creates valid closures with correct code-ptr
3. Prove apply-with-thunk using thunk context
4. Prove composition theorems

## Trusted Base: Encoding Axioms

The only remaining postulates are encoding axioms in `Once.Postulates`:

| Postulate | Purpose |
|-----------|---------|
| `encode-pair-fst` | Read fst from encoded pair |
| `encode-pair-snd` | Read snd from encoded pair |
| `encode-sum-tag` | Read tag from encoded sum |
| `encode-sum-value` | Read value from encoded sum |
| `encode-closure-env` | Read env from encoded closure |
| `encode-closure-code` | Read code-ptr from encoded closure |
| `encode-pair-construct` | Memory layout is valid pair encoding |

These are the **intentional trusted base** - they specify how semantic values are represented in memory. They cannot be proven without a model of memory that includes allocation semantics.

## Summary

The key insight is recognizing that **apply is only meaningful in composition with curry**. By proving them together with the thunk code in the same program, we achieve full proofs while respecting the categorical semantics of closures.

This architecture:
- Eliminates all non-encoding postulates
- Uses composition theorems instead of isolated proofs
- Tracks stack invariants mechanically
- Applies uniformly across all backends
