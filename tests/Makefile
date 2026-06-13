# Integration tests for Once compiler
#
# Run from tests/ directory:
#   make test        - run all tests
#   make clean       - remove build artifacts
#
# Or run individual tests:
#   make test-exe    - test executable mode
#   make test-lib    - test library mode
#   make test-target - test --target flag
#   make test-strata - test --strata flag
#
# Convention: every phony target carries its own `.PHONY: <target>` line
# immediately above it (not one shared list) so adding/removing a target
# touches only its own block and never collides in merges.

ONCE = cd ../compiler && cabal run --verbose=0 once --
GCC = gcc
BUILD = .build
TESTS_DIR = $(shell pwd)

.PHONY: all
all: test

# Create build directory
$(BUILD):
	mkdir -p $(BUILD)

#-----------------------------------------------------------------------------
# Test: Executable mode (--exe)
#-----------------------------------------------------------------------------

.PHONY: test-exe
test-exe: $(BUILD) test-exe-simple test-exe-import
	@echo "==> --exe tests passed"

.PHONY: test-exe-simple
test-exe-simple: $(BUILD)
	@echo "Testing: simple.once --exe"
	$(ONCE) build --exe --strata $(TESTS_DIR)/Strata $(TESTS_DIR)/simple.once -o $(TESTS_DIR)/$(BUILD)/simple
	$(GCC) -o $(BUILD)/simple $(BUILD)/simple.c
	$(BUILD)/simple
	@echo "  OK"

.PHONY: test-exe-import
test-exe-import: $(BUILD)
	@echo "Testing: with-import.once --exe --strata"
	$(ONCE) build --exe --strata $(TESTS_DIR)/Strata $(TESTS_DIR)/with-import.once -o $(TESTS_DIR)/$(BUILD)/with-import
	$(GCC) -o $(BUILD)/with-import $(BUILD)/with-import.c
	$(BUILD)/with-import
	@echo "  OK"

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
# Test: Target flag (--target)
#-----------------------------------------------------------------------------

.PHONY: test-target
test-target: $(BUILD) test-target-c test-target-invalid test-target-unimplemented
	@echo "==> --target tests passed"

.PHONY: test-target-c
test-target-c: $(BUILD)
	@echo "Testing: --target c"
	$(ONCE) build --exe --target c --strata $(TESTS_DIR)/Strata $(TESTS_DIR)/simple.once -o $(TESTS_DIR)/$(BUILD)/target-c
	$(GCC) -o $(BUILD)/target-c $(BUILD)/target-c.c
	$(BUILD)/target-c
	@echo "  OK"

.PHONY: test-target-invalid
test-target-invalid: $(BUILD)
	@echo "Testing: --target invalid (should fail)"
	@! ($(ONCE) build --exe --target invalid --strata $(TESTS_DIR)/Strata $(TESTS_DIR)/simple.once -o $(TESTS_DIR)/$(BUILD)/target-invalid 2>/dev/null)
	@echo "  OK (rejected as expected)"

.PHONY: test-target-unimplemented
test-target-unimplemented: $(BUILD)
	@echo "Testing: --target x86_64 (should fail gracefully)"
	$(ONCE) build --exe --target x86_64 --strata $(TESTS_DIR)/Strata $(TESTS_DIR)/simple.once -o $(TESTS_DIR)/$(BUILD)/target-x86 2>&1 | grep -q "not yet implemented"
	@echo "  OK (graceful error)"

#-----------------------------------------------------------------------------
# Test: Strata flag (--strata)
#-----------------------------------------------------------------------------

.PHONY: test-strata
test-strata: $(BUILD) test-strata-explicit test-strata-import
	@echo "==> --strata tests passed"

.PHONY: test-strata-explicit
test-strata-explicit: $(BUILD)
	@echo "Testing: --strata explicit path"
	$(ONCE) build --exe --strata $(TESTS_DIR)/Strata $(TESTS_DIR)/with-import.once -o $(TESTS_DIR)/$(BUILD)/strata-explicit
	@test -f $(BUILD)/strata-explicit.c
	@echo "  OK"

.PHONY: test-strata-import
test-strata-import: $(BUILD)
	@echo "Testing: import with D. abbreviation"
	$(ONCE) build --exe --strata $(TESTS_DIR)/Strata $(TESTS_DIR)/with-import.once -o $(TESTS_DIR)/$(BUILD)/strata-import
	@grep -q "once_mySwap" $(BUILD)/strata-import.c
	@echo "  OK"

#-----------------------------------------------------------------------------
# Test: Polymorphic user defs + NT desugaring (plan 0.6 Phase C.6)
#-----------------------------------------------------------------------------

.PHONY: test-poly
test-poly: $(BUILD)
	@echo "Testing: poly-defs.once --check"
	$(ONCE) check $(TESTS_DIR)/poly-defs.once | grep -q "Typecheck OK"
	@echo "  OK"

#-----------------------------------------------------------------------------
# Test: Heap-mode exit-code suite (layer0-4 + pure catas)
#
# Builds every compiler/test/*.once with a declared expected exit code using
# the canonical heap-mode params (--alloc heap --no-optimize), runs the
# binary, and checks the exit code. This is the RUNTIME net: the Agda proofs
# are value-level, so a pass that drops an observable SigOp (e.g. the
# optimizer's →Unit ⇒ terminal rule) stays green there but is caught here.
#-----------------------------------------------------------------------------

.PHONY: test-heap-exit
test-heap-exit:
	@echo "Testing: heap-mode exit-code suite (--alloc heap --no-optimize)"
	$(TESTS_DIR)/run-exit-tests.sh

#-----------------------------------------------------------------------------
# Run all tests
#-----------------------------------------------------------------------------

.PHONY: test
test: test-exe test-lib test-target test-strata test-poly test-heap-exit
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
