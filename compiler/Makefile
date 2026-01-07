# Makefile for Once compiler
#
# Usage:
#   make test          - Run all tests (C + x86 backends)
#   make test-c        - Run C backend tests only
#   make test-x86      - Run x86 backend tests only
#   make test-quick    - Run fast tests (skip integration tests)
#   make test-escape   - Test escape analysis optimization
#   make build         - Build the compiler (with nix)
#   make clean         - Clean build artifacts

.PHONY: all build test test-c test-x86 test-quick test-escape clean

# Default target
all: build test

# Build the compiler using nix
build:
	nix build

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

# Run codegen tests only (fastest)
test-codegen:
	stack test --ta '-p "/codegen/"'

# Run with verbose output
test-verbose:
	stack test --ta '--hide-successes'

# Test escape analysis optimization
# Note: The test program now uses IO Unit signature and exit syscall.
# With --exe flag, the compiler should automatically invoke gcc when the main
# function has type IO Unit. However, if automatic compilation isn't working,
# the manual gcc step below will still compile the generated C code.
test-escape: build
	@echo "Testing escape analysis optimization..."
	@echo "Building simple-refcount-test.once..."
	./result/bin/once build \
		--exe --interp ../Strata/Interpretations/Linux \
		../examples/simple-refcount-test.once \
		-o ../examples/simple-refcount-test
	@# Check if executable was created automatically
	@if [ -f ../examples/simple-refcount-test ]; then \
		echo "✓ Executable created automatically by compiler"; \
	else \
		echo "Note: Automatic gcc compilation not available, compiling manually..."; \
		gcc -o ../examples/simple-refcount-test \
			../examples/simple-refcount-test.c \
			-O2 -Wall; \
	fi
	@echo "Running test..."
	@../examples/simple-refcount-test
	@if [ $$? -eq 54 ]; then \
		echo "✓ Escape analysis test passed (exit code: 54)"; \
	else \
		echo "✗ Escape analysis test failed"; \
		exit 1; \
	fi

# Clean build artifacts
clean:
	stack clean
	rm -rf .stack-work
	rm -f ../examples/*.c ../examples/*.exe result
