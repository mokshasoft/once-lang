# Makefile for Once compiler
#
# Usage:
#   make test          - Run all tests (C + x86 backends)
#   make test-c        - Run C backend tests only
#   make test-x86      - Run x86 backend tests only
#   make test-quick    - Run fast tests (skip integration tests)
#   make build         - Build the compiler
#   make clean         - Clean build artifacts
#
# Build tool: cabal. Stack is NOT used — Stack 3.7.1 + Nix triggers a
# self-referential thunk in Stack's GHC-version resolution that aborts
# with `<<loop>>` before any user code runs. See
# plans/0.2.4-categorical-layer-0.md for the diagnosis. The nix flake
# uses callCabal2nix and is also cabal-based.

.PHONY: all build test test-c test-x86 test-quick test-x86-level0 test-codegen test-verbose clean

# Default target
all: build test

# Build the compiler
build:
	cabal build

# Run all tests
test:
	cabal test

# Run only C backend tests
test-c:
	cabal test --test-options='-p "/Backend.C/"'

# Run only x86 backend tests
test-x86:
	cabal test --test-options='-p "/Backend.X86/"'

# Run quick tests (excluding slow integration tests)
test-quick:
	cabal test --test-options='-p "!/executable/"'

# Run Layer 0 tests only (isolated from MAlonzo issues)
test-x86-level0:
	cabal test --test-options='-p "/Layer0/"'

# Run codegen tests only (fastest)
test-codegen:
	cabal test --test-options='-p "/codegen/"'

# Run with verbose output
test-verbose:
	cabal test --test-options='--hide-successes'

# Clean build artifacts
clean:
	cabal clean
