# Makefile for Once example programs
#
# This Makefile builds and tests example programs using the Once compiler.
# Run from the examples/ directory.
#
# Usage:
#   make                - Build and run all Linux tests (C + native)
#   make c              - Build and run C backend tests
#   make native         - Build and run native x86_64 tests
#   make native-qemu    - Build and run native arm64/riscv64 tests (requires qemu)
#   make seL4           - Build and run seL4 examples (requires nix)
#   make full           - Run all tests including seL4
#   make clean          - Remove build artifacts

.PHONY: all c native native-qemu seL4 full clean

# Get absolute path to examples directory
EXAMPLES_DIR := $(shell pwd)
REPO_ROOT := $(EXAMPLES_DIR)/..

# Build directory
BUILD := $(REPO_ROOT)/.build

# Strata path
STRATA := $(REPO_ROOT)/Strata

# Once compiler (run from compiler directory)
ONCE := cd $(REPO_ROOT)/compiler && cabal run --verbose=0 once --

# Default target
all: c native
	@echo "All tests passed!"

# C backend tests
c: $(BUILD)/hi-c $(BUILD)/hello-c $(BUILD)/let-test-c $(BUILD)/arith-test-c $(BUILD)/fizzbuzz-c
	@echo "Running C backend tests..."
	$(BUILD)/hi-c && echo "hi-c: PASS"
	$(BUILD)/hello-c && echo "hello-c: PASS"
	$(BUILD)/let-test-c && echo "let-test-c: PASS"
	$(BUILD)/arith-test-c && echo "arith-test-c: PASS"
	$(BUILD)/fizzbuzz-c && echo "fizzbuzz-c: PASS"
	@echo "C backend tests passed!"

$(BUILD)/hi-c: hi.once
	@mkdir -p $(BUILD)
	$(ONCE) build --exe --target c --strata $(STRATA) $(EXAMPLES_DIR)/hi.once -o $(BUILD)/hi-c

$(BUILD)/hello-c: hello.once
	@mkdir -p $(BUILD)
	$(ONCE) build --exe --target c --strata $(STRATA) $(EXAMPLES_DIR)/hello.once -o $(BUILD)/hello-c

$(BUILD)/let-test-c: let-test.once
	@mkdir -p $(BUILD)
	$(ONCE) build --exe --target c --strata $(STRATA) $(EXAMPLES_DIR)/let-test.once -o $(BUILD)/let-test-c

$(BUILD)/arith-test-c: arith-test.once
	@mkdir -p $(BUILD)
	$(ONCE) build --exe --target c --strata $(STRATA) $(EXAMPLES_DIR)/arith-test.once -o $(BUILD)/arith-test-c

$(BUILD)/fizzbuzz-c: competitive/fizzbuzz.once
	@mkdir -p $(BUILD)
	$(ONCE) build --exe --target c --strata $(STRATA) $(EXAMPLES_DIR)/competitive/fizzbuzz.once -o $(BUILD)/fizzbuzz-c

# Native x86_64 tests (runs on host)
native: $(BUILD)/hi-x86_64
	@echo "Running native x86_64 tests..."
	$(BUILD)/hi-x86_64 && echo "hi-x86_64: PASS"
	@echo "Native x86_64 tests passed!"

$(BUILD)/hi-x86_64: hi.once
	@mkdir -p $(BUILD)
	$(ONCE) build --exe --target x86_64 --strata $(STRATA) $(EXAMPLES_DIR)/hi.once -o $(BUILD)/hi-x86_64

# Native cross-compilation tests (requires qemu + cross-compilers)
# Run with: nix develop ..#default --command make native-qemu
native-qemu: native-arm64 native-riscv64
	@echo "Native cross-compilation tests passed!"

native-arm64: $(BUILD)/hi-arm64
	@echo "Running native ARM64 tests (via qemu)..."
	qemu-aarch64 -L /usr/aarch64-linux-gnu $(BUILD)/hi-arm64 && echo "hi-arm64: PASS"

native-riscv64: $(BUILD)/hi-riscv64
	@echo "Running native RISC-V64 tests (via qemu)..."
	qemu-riscv64 -L /usr/riscv64-linux-gnu $(BUILD)/hi-riscv64 && echo "hi-riscv64: PASS"

$(BUILD)/hi-arm64: hi.once
	@mkdir -p $(BUILD)
	CC=aarch64-linux-gnu-gcc LD=aarch64-linux-gnu-ld \
	$(ONCE) build --exe --target arm64 --strata $(STRATA) $(EXAMPLES_DIR)/hi.once -o $(BUILD)/hi-arm64

$(BUILD)/hi-riscv64: hi.once
	@mkdir -p $(BUILD)
	CC=riscv64-linux-gnu-gcc LD=riscv64-linux-gnu-ld \
	$(ONCE) build --exe --target riscv64 --strata $(STRATA) $(EXAMPLES_DIR)/hi.once -o $(BUILD)/hi-riscv64

# seL4 examples (requires nix)
seL4:
	@echo "Building seL4 examples..."
	cd $(EXAMPLES_DIR)/seL4 && nix build
	@echo "Running seL4 echo test (30s timeout)..."
	@timeout 30 $(EXAMPLES_DIR)/seL4/result/bin/simulate 2>&1 | tee /tmp/sel4-output.txt | tail -20 || true
	@grep -q "All tests passed" /tmp/sel4-output.txt && echo "seL4: PASS" || (echo "seL4: FAIL" && exit 1)
	@echo "seL4 tests passed!"

# Full test suite including seL4
full: all seL4
	@echo "=== All tests passed (Linux + seL4) ==="

clean:
	rm -f $(BUILD)/hi-c $(BUILD)/hello-c $(BUILD)/let-test-c $(BUILD)/arith-test-c $(BUILD)/fizzbuzz-c
	rm -f $(BUILD)/hi-x86_64 $(BUILD)/hi-arm64 $(BUILD)/hi-riscv64
	rm -f $(BUILD)/*.s $(BUILD)/*.o
