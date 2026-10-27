# Makefile for Once example programs
#
# Builds every example and checks what it does. Once has no strings yet, so a
# program is observed by its exit code; each one's expected code is below.
#
# Usage (from examples/):
#   make                - check, then build and run on x86_64 and x86_32
#   make check          - type-check every example; build the libraries
#   make x86_64         - build and run the programs on x86-64
#   make x86_32         - build and run the programs on x86-32
#   make riscv64        - cross-build and run under qemu-riscv64
#                         (needs riscv64-unknown-linux-gnu-{as,ld,objcopy}, e.g. `nix develop`)
#   make seL4           - Build and run the seL4 echo test (requires nix). Parked: it
#                         runs hand-written C, not Once (plan 0.127); not part of `make`
#   make clean          - Remove build artifacts
#
# The compiler is `once` on PATH; override with e.g. `make ONCE=../result/bin/once`.

.PHONY: all check x86_64 x86_32 riscv64 seL4 clean

ONCE ?= once

EXAMPLES_DIR := $(shell pwd)
REPO_ROOT := $(EXAMPLES_DIR)/..
BUILD := $(REPO_ROOT)/.build/examples

# program:expected-exit-code
PROGRAMS := hi:0 hello:42 arith-simple:13 let-test:48 competitive/fizzbuzz:7

# Type-checked only (no `main`); the libraries are also built to assembly
CHECKED := qtt categorical swap
LIBRARIES := categorical swap

RISCV_ENV := AS=riscv64-unknown-linux-gnu-as LD=riscv64-unknown-linux-gnu-ld \
             OBJCOPY=riscv64-unknown-linux-gnu-objcopy

# $(call run-all,TARGET,ENV,RUNNER): build each program for TARGET and check its exit code
define run-all
	@mkdir -p $(BUILD)/$(1)
	@for p in $(PROGRAMS); do \
	  name=$${p%%:*}; want=$${p##*:}; out=$(BUILD)/$(1)/$$(basename $$name); \
	  $(2) $(ONCE) build --target $(1) $(EXAMPLES_DIR)/$$name.once -o $$out > /dev/null || exit 1; \
	  $(3) $$out; got=$$?; \
	  if [ $$got -eq $$want ]; then echo "$(1) $$name: PASS ($$got)"; \
	  else echo "$(1) $$name: FAIL (exit $$got, expected $$want)"; exit 1; fi; \
	done
endef

all: check x86_64 x86_32
	@echo "All examples passed!"

check:
	@mkdir -p $(BUILD)/lib
	@for f in $(CHECKED); do \
	  $(ONCE) check $(EXAMPLES_DIR)/$$f.once > /dev/null || exit 1; echo "check $$f: PASS"; \
	done
	@for f in $(LIBRARIES); do \
	  $(ONCE) build --lib $(EXAMPLES_DIR)/$$f.once -o $(BUILD)/lib/$$f > /dev/null || exit 1; \
	  echo "library $$f: PASS"; \
	done

x86_64:
	$(call run-all,x86_64,,)

x86_32:
	$(call run-all,x86_32,,)

riscv64:
	$(call run-all,riscv64,$(RISCV_ENV),qemu-riscv64)

# seL4 examples (requires nix)
seL4:
	@echo "Building seL4 examples..."
	cd $(EXAMPLES_DIR)/seL4 && nix build
	@echo "Running seL4 echo test (30s timeout)..."
	@timeout 30 $(EXAMPLES_DIR)/seL4/result/bin/simulate 2>&1 | tee /tmp/sel4-output.txt | tail -20 || true
	@grep -q "All tests passed" /tmp/sel4-output.txt && echo "seL4: PASS" || (echo "seL4: FAIL" && exit 1)
	@echo "seL4 tests passed!"

clean:
	rm -rf $(BUILD)
