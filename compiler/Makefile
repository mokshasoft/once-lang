# Makefile for Once compiler
#
# Usage:
#   make test          - Run all tests (C + x86 backends)
#   make test-c        - Run C backend tests only
#   make test-x86      - Run x86 backend tests only
#   make test-quick    - Run fast tests (skip integration tests)
#   make build         - Build the compiler
#   make clean         - Clean build artifacts

.PHONY: all build test test-c test-x86 test-quick test-x86-level0 clean

# Default target
all: build test

# Build the compiler
build:
	stack build

# Run all tests
test:
	stack test

# Run only C backend tests
test-c:
	stack test --ta '-p "/Backend.C/"'

# Run only x86 backend tests
test-x86:
	stack test --ta '-p "/Backend.X86/"'

# Run quick tests (excluding slow integration tests)
test-quick:
	stack test --ta '-p "!/executable/"'

# Run Layer 0 tests only (isolated from MAlonzo issues)
test-x86-level0:
	stack test --ta '-p "/Layer0/"'

# Run codegen tests only (fastest)
test-codegen:
	stack test --ta '-p "/codegen/"'

# Run with verbose output
test-verbose:
	stack test --ta '--hide-successes'

# Clean build artifacts
clean:
	stack clean
	rm -rf .stack-work
