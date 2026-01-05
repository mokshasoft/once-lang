# Once Formal Verification Documentation

This directory contains all documentation related to the formal verification of the Once compiler.

## Directory Structure

### `core/` - Essential Documentation (**Start Here**)

The actively maintained documentation for verification work:

- **[proof-instructions.md](core/proof-instructions.md)** - **MANDATORY RULES** for all verification work
  - Prime Directive: No Shortcuts
  - Star-based proof patterns
  - Backend proof architecture (stateful proofs)
  - Build commands and workflows

- **[problems-and-solutions.md](core/problems-and-solutions.md)** - Active problem tracking
  - Current problems and their priority
  - Solved patterns and solutions
  - Strategy documentation

- **[verification-plan.md](core/verification-plan.md)** - Roadmap for full compiler verification
  - Current status and phase tracking
  - Implementation plans
  - Success criteria

- **[what-is-proven.md](core/what-is-proven.md)** - Current verification status
  - Proof completion summary
  - Remaining postulates
  - Verification scope

### `architecture/` - Backend-Specific Architectures

Detailed architecture documentation for each backend:

- **[x86-64-backend-verification-plan.md](architecture/x86-64-backend-verification-plan.md)** - x86-64 stateful proof architecture (RECOMMENDED approach)
- **[aarch64-backend-verification-plan.md](architecture/aarch64-backend-verification-plan.md)** - AArch64 backend architecture (in progress)
- **[riscv64-backend-verification-plan.md](architecture/riscv64-backend-verification-plan.md)** - RISC-V backend architecture (non-stateful)

### `guides/` - How-To Guides and Examples

Practical guides for implementing proofs:

- **[stateful-runner-example.md](guides/stateful-runner-example.md)** - Example of stateful proof pattern
- **[apply-proof-strategy.md](guides/apply-proof-strategy.md)** - Strategy for proving apply correctness
- **[encoding-postulate-elimination-plan.md](guides/encoding-postulate-elimination-plan.md)** - How to eliminate encoding postulates
- **[allocation-strategies-and-escape-analysis.md](guides/allocation-strategies-and-escape-analysis.md)** - Memory allocation strategies, escape analysis, and stack vs heap tradeoffs
- **[proof-modularization-comparison.md](guides/proof-modularization-comparison.md)** - Comparing ARM and x86 proof modularization approaches (specialized records vs split modules)

### `historical/` - Historical Documentation

Completed investigations and lessons learned:

#### `historical/exchange-problem/` - Exchange Problem Investigation

Complete investigation into the exchange₆ postulate problem:
- cogent-investigation.md
- depth-examples.md
- depth-limit-implementation.md
- exchange-problem-analysis.md
- exchange-solutions-reconsidered.md
- extrinsic-typing-impact.md

#### Other Historical Documents

- **[lessons-learned.md](historical/lessons-learned.md)** - Lessons from verification work
- **[proof-analysis.md](historical/proof-analysis.md)** - Historical proof analysis
- **[proof-refactoring-proposal.md](historical/proof-refactoring-proposal.md)** - Completed refactoring proposals
- **[shareable-proof-refactor.md](historical/shareable-proof-refactor.md)** - Completed refactoring work
- **[fix-semantics-options.md](historical/fix-semantics-options.md)** - Resolved semantics issues
- **[full-verification-compiler-stack.md](historical/full-verification-compiler-stack.md)** - Historical verification stack documentation

### `sessions/` - Session Summaries

Documentation from specific verification sessions:

- **[VERIFICATION-SESSION-SUMMARY.md](sessions/VERIFICATION-SESSION-SUMMARY.md)** - Session summaries and notes
- **[qtt-step3-todos.md](sessions/qtt-step3-todos.md)** - QTT step 3 task tracking

## Quick Start

1. **New to Once verification?** Start with [proof-instructions.md](core/proof-instructions.md)
2. **Working on a task?** Check [problems-and-solutions.md](core/problems-and-solutions.md) for current priorities
3. **Implementing a new backend?** Use [x86-64-backend-verification-plan.md](architecture/x86-64-backend-verification-plan.md) as the reference
4. **Checking verification status?** See [what-is-proven.md](core/what-is-proven.md)

## Key Principles

From [proof-instructions.md](core/proof-instructions.md):

1. **No Inline Postulates** - Every postulate is unfinished work; goal is ZERO inline postulates
2. **Star-Based Proofs** - All proofs use the Star relation (no fuel-based proofs)
3. **Stateful Proofs** - Use stateful proof architecture (IRStarResultS) to eliminate encoding postulates
4. **Compiler Correctness** - We prove the compiler works for arbitrary programs, not specific program correctness

## Documentation Organization Philosophy

- **Core**: Actively maintained, always current
- **Architecture**: Reference material for backend implementation
- **Guides**: Practical how-to documents
- **Historical**: Preserved for reference, may be outdated
- **Sessions**: Time-bound session notes and summaries
