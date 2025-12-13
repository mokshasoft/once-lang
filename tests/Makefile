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

ONCE = cd ../compiler && stack exec -- once
GCC = gcc
BUILD = .build
TESTS_DIR = $(shell pwd)

.PHONY: all test clean test-exe test-lib test-target test-strata

all: test

# Create build directory
$(BUILD):
	mkdir -p $(BUILD)

#-----------------------------------------------------------------------------
# Test: Executable mode (--exe)
#-----------------------------------------------------------------------------

test-exe: $(BUILD) test-exe-simple test-exe-import
	@echo "==> --exe tests passed"

test-exe-simple: $(BUILD)
	@echo "Testing: simple.once --exe"
	$(ONCE) build --exe --strata $(TESTS_DIR)/Strata $(TESTS_DIR)/simple.once -o $(TESTS_DIR)/$(BUILD)/simple
	$(GCC) -o $(BUILD)/simple $(BUILD)/simple.c
	$(BUILD)/simple
	@echo "  OK"

test-exe-import: $(BUILD)
	@echo "Testing: with-import.once --exe --strata"
	$(ONCE) build --exe --strata $(TESTS_DIR)/Strata $(TESTS_DIR)/with-import.once -o $(TESTS_DIR)/$(BUILD)/with-import
	$(GCC) -o $(BUILD)/with-import $(BUILD)/with-import.c
	$(BUILD)/with-import
	@echo "  OK"

#-----------------------------------------------------------------------------
# Test: Library mode (--lib)
#-----------------------------------------------------------------------------

test-lib: $(BUILD) test-lib-basic
	@echo "==> --lib tests passed"

test-lib-basic: $(BUILD)
	@echo "Testing: lib-test.once --lib"
	$(ONCE) build --lib $(TESTS_DIR)/lib-test.once -o $(TESTS_DIR)/$(BUILD)/lib-test
	@test -f $(BUILD)/lib-test.h || (echo "FAIL: missing .h file"; exit 1)
	@test -f $(BUILD)/lib-test.c || (echo "FAIL: missing .c file"; exit 1)
	@echo "  OK"

#-----------------------------------------------------------------------------
# Test: Target flag (--target)
#-----------------------------------------------------------------------------

test-target: $(BUILD) test-target-c test-target-invalid test-target-unimplemented
	@echo "==> --target tests passed"

test-target-c: $(BUILD)
	@echo "Testing: --target c"
	$(ONCE) build --exe --target c --strata $(TESTS_DIR)/Strata $(TESTS_DIR)/simple.once -o $(TESTS_DIR)/$(BUILD)/target-c
	$(GCC) -o $(BUILD)/target-c $(BUILD)/target-c.c
	$(BUILD)/target-c
	@echo "  OK"

test-target-invalid: $(BUILD)
	@echo "Testing: --target invalid (should fail)"
	@! ($(ONCE) build --exe --target invalid --strata $(TESTS_DIR)/Strata $(TESTS_DIR)/simple.once -o $(TESTS_DIR)/$(BUILD)/target-invalid 2>/dev/null)
	@echo "  OK (rejected as expected)"

test-target-unimplemented: $(BUILD)
	@echo "Testing: --target x86_64 (should fail gracefully)"
	$(ONCE) build --exe --target x86_64 --strata $(TESTS_DIR)/Strata $(TESTS_DIR)/simple.once -o $(TESTS_DIR)/$(BUILD)/target-x86 2>&1 | grep -q "not yet implemented"
	@echo "  OK (graceful error)"

#-----------------------------------------------------------------------------
# Test: Strata flag (--strata)
#-----------------------------------------------------------------------------

test-strata: $(BUILD) test-strata-explicit test-strata-import
	@echo "==> --strata tests passed"

test-strata-explicit: $(BUILD)
	@echo "Testing: --strata explicit path"
	$(ONCE) build --exe --strata $(TESTS_DIR)/Strata $(TESTS_DIR)/with-import.once -o $(TESTS_DIR)/$(BUILD)/strata-explicit
	@test -f $(BUILD)/strata-explicit.c
	@echo "  OK"

test-strata-import: $(BUILD)
	@echo "Testing: import with D. abbreviation"
	$(ONCE) build --exe --strata $(TESTS_DIR)/Strata $(TESTS_DIR)/with-import.once -o $(TESTS_DIR)/$(BUILD)/strata-import
	@grep -q "once_mySwap" $(BUILD)/strata-import.c
	@echo "  OK"

#-----------------------------------------------------------------------------
# Run all tests
#-----------------------------------------------------------------------------

test: test-exe test-lib test-target test-strata
	@echo ""
	@echo "=========================================="
	@echo "All integration tests passed!"
	@echo "=========================================="

#-----------------------------------------------------------------------------
# Clean
#-----------------------------------------------------------------------------

clean:
	rm -rf $(BUILD)
