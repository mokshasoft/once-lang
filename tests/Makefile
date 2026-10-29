# Integration tests for Once compiler
#
# Run from tests/ directory:
#   make test        - run all tests
#   make clean       - remove build artifacts
#
# Or run individual tests:
#   make test-lib       - test library mode
#   make test-poly      - polymorphic definitions type-check
#   make test-heap-exit - build and run every compiler/test exit test (x86_64)
#
# Convention: every phony target carries its own `.PHONY: <target>` line
# immediately above it (not one shared list) so adding/removing a target
# touches only its own block and never collides in merges.

ONCE = cd ../compiler && cabal run --verbose=0 once --
BUILD = .build
TESTS_DIR = $(shell pwd)

.PHONY: all
all: test

# Create build directory
$(BUILD):
	mkdir -p $(BUILD)

#-----------------------------------------------------------------------------
# Test: Library mode (--lib)
#-----------------------------------------------------------------------------

.PHONY: test-lib
test-lib: $(BUILD) test-lib-basic test-lib-multi
	@echo "==> library tests passed"

# A library has no `main`; its concrete top-level functions are the interface
# (D008 / "concrete = interface"). The C library backend (--lib) is not yet
# implemented, so we compile to x86_64 assembly (no entry point) and check the
# .s is produced — i.e. a no-main library is accepted and codegens.
.PHONY: test-lib-basic
test-lib-basic: $(BUILD)
	@echo "Testing: lib-test.once (library, no main -> x86_64 asm)"
	$(ONCE) build --target x86_64 $(TESTS_DIR)/lib-test.once -o $(TESTS_DIR)/$(BUILD)/lib-test
	@test -f $(BUILD)/lib-test.s || (echo "FAIL: missing .s file"; exit 1)
	@echo "  OK"

.PHONY: test-lib-multi
test-lib-multi: $(BUILD)
	@echo "Testing: lib-multi.once (multi-function library -> x86_64 asm)"
	$(ONCE) build --target x86_64 $(TESTS_DIR)/lib-multi.once -o $(TESTS_DIR)/$(BUILD)/lib-multi
	@test -f $(BUILD)/lib-multi.s || (echo "FAIL: missing .s file"; exit 1)
	@echo "  OK"

#-----------------------------------------------------------------------------
# Test: Polymorphic user defs + NT desugaring (plan 0.6 Phase C.6)
#-----------------------------------------------------------------------------

.PHONY: test-poly
test-poly: $(BUILD)
	@echo "Testing: poly-defs.once --check"
	$(ONCE) check $(TESTS_DIR)/poly-defs.once | grep -q "Typecheck OK"
	@echo "Testing: poly-bare-ref.once --check"
	$(ONCE) check $(TESTS_DIR)/poly-bare-ref.once | grep -q "Typecheck OK"
	@echo "  OK"

#-----------------------------------------------------------------------------
# Test: Heap-mode exit-code suite (layer0-4 + pure catas)
#
# Builds every compiler/test/*.once with a declared expected exit code using
# the canonical heap-mode params (--alloc heap), once with --no-optimize and
# once without, runs both binaries, checks the exit codes and compares the
# outputs. This is the RUNTIME net: the Agda proofs
# are value-level, so a pass that drops an observable SigOp (e.g. the
# optimizer's →Unit ⇒ terminal rule) stays green there but is caught here.
#-----------------------------------------------------------------------------

.PHONY: test-heap-exit
test-heap-exit:
	@echo "Testing: heap-mode exit-code suite (--alloc heap, with and without the optimizer)"
	$(TESTS_DIR)/run-exit-tests.sh

#-----------------------------------------------------------------------------
# Run all tests
#-----------------------------------------------------------------------------

.PHONY: test
test: test-lib test-poly test-heap-exit
	@echo ""
	@echo "=========================================="
	@echo "All integration tests passed!"
	@echo "=========================================="

#-----------------------------------------------------------------------------
# Clean
#-----------------------------------------------------------------------------

.PHONY: clean
clean:
	rm -rf $(BUILD)
