# Makefile for the Once bootstrap normalizer verification
#
# Run from bootstrap/ directory: make -C normalizer
# Or from normalizer/ directory with: cd .. && agda normalizer/Main.agda

AGDA := cd .. && agda
AGDA_FILES := $(shell find . -name "*.agda")

.PHONY: all tcb0 main check postulates postulates-summary clean help

# Default: type-check both TCB0 (postulate-free) and Main
all: tcb0 main

# Type-check TCB0 with --safe flag (postulate-free verification)
# This is the trusted computing base - no axioms required
tcb0:
	@echo "=== Verifying TCB0 (postulate-free, --safe) ==="
	$(AGDA) --safe normalizer/TCB0.agda
	@echo "=== TCB0 verification complete ==="

# Type-check Main (full theory with postulates)
# Uses established mathematical results (strong normalization, confluence)
main:
	@echo "=== Verifying Main (with postulates) ==="
	$(AGDA) normalizer/Main.agda
	@echo "=== Main verification complete ==="

# Type-check all Agda files individually
check:
	@echo "Type-checking all Agda files..."
	@for f in $(AGDA_FILES); do \
		echo "Checking $$f"; \
		(cd .. && agda "normalizer/$$f") || exit 1; \
	done
	@echo "All files type-check successfully."

# Check specific module groups
check-syntax:
	$(AGDA) normalizer/Syntax/Types.agda
	$(AGDA) normalizer/Syntax/CCC.agda
	$(AGDA) normalizer/Syntax/NoRedex.agda
	$(AGDA) normalizer/Syntax/NormalForm.agda
	$(AGDA) normalizer/Syntax/BetaNormalForm.agda

check-encoding:
	$(AGDA) normalizer/Encoding/Encoding.agda
	$(AGDA) normalizer/Encoding/TermFunctor.agda
	$(AGDA) normalizer/Encoding/Catamorphisms.agda

check-combinators:
	$(AGDA) normalizer/Combinators/Chain.agda
	$(AGDA) normalizer/Combinators/ReductionCombinators.agda
	$(AGDA) normalizer/Combinators/DispatchCombinators.agda
	$(AGDA) normalizer/Combinators/OutIn.agda

check-theory:
	$(AGDA) normalizer/Theory/Spec/AlgebraSpec.agda
	$(AGDA) normalizer/Theory/Spec/NormalizerSpec.agda
	$(AGDA) normalizer/Theory/GeneralCorrectness/Correctness.agda

# Quick grep for postulate blocks
postulates-quick:
	@grep -r "^postulate" * --include='*.agda'

# List all postulates with context
postulates:
	@echo "=== Postulates in the codebase ==="
	@for f in $(AGDA_FILES); do \
		count=$$(awk '/^postulate/{flag=1; next} /^[^ ]/{flag=0} flag && /^  [a-zA-Z⌜_].*:/' "$$f" | wc -l); \
		if [ "$$count" -gt 0 ]; then \
			echo ""; \
			echo "=== $$f ($$count postulates) ==="; \
			awk '/^postulate/{flag=1; next} /^[^ ]/{flag=0} flag && /^  [a-zA-Z⌜_].*:/{print}' "$$f"; \
		fi \
	done

# Summary of postulates per file
postulates-summary:
	@echo "=== Postulate Summary ==="
	@total=0; \
	for f in $(AGDA_FILES); do \
		count=$$(awk '/^postulate/{flag=1; next} /^[^ ]/{flag=0} flag && /^  [a-zA-Z⌜_].*:/' "$$f" | wc -l); \
		if [ "$$count" -gt 0 ]; then \
			echo "$$f: $$count"; \
			total=$$((total + count)); \
		fi \
	done; \
	echo "---"; \
	echo "Total: $$total postulates"

# List proven theorems (non-postulated definitions)
theorems:
	@echo "=== Key Proven Theorems ==="
	@grep -h "^[a-zA-Z⌜_].*:.*⟶\*\|^[a-zA-Z⌜_].*:.*≡\|^[a-zA-Z⌜_].*:.*⇒" $(AGDA_FILES) | \
		grep -v "postulate" | head -50

# Search for a pattern in all Agda files
search:
	@if [ -z "$(PATTERN)" ]; then \
		echo "Usage: make search PATTERN='your pattern'"; \
	else \
		grep -rn "$(PATTERN)" --include="*.agda"; \
	fi

# Find all holes (unfinished proofs)
holes:
	@echo "=== Holes in the codebase ==="
	@grep -rn "{!" --include="*.agda" || echo "No holes found."

# Count lines of code
loc:
	@echo "=== Lines of Code ==="
	@wc -l $(AGDA_FILES) | tail -1

# Clean generated files
clean:
	find . -name "*.agdai" -delete
	find . -name "MAlonzo" -type d -exec rm -rf {} + 2>/dev/null || true

# Help
help:
	@echo "Available targets:"
	@echo ""
	@echo "  Primary verification:"
	@echo "    all              - Verify both TCB0 and Main (default)"
	@echo "    tcb0             - Verify postulate-free core (--safe flag)"
	@echo "    main             - Verify full theorem (uses postulates)"
	@echo ""
	@echo "  Module checks:"
	@echo "    check            - Type-check all Agda files individually"
	@echo "    check-syntax     - Check Syntax/ modules"
	@echo "    check-encoding   - Check Encoding/ modules"
	@echo "    check-combinators - Check Combinators/ modules"
	@echo "    check-theory     - Check Theory/ modules"
	@echo ""
	@echo "  Analysis:"
	@echo "    postulates-quick   - Quick grep for postulate blocks"
	@echo "    postulates         - List all postulates with their types"
	@echo "    postulates-summary - Summary count of postulates per file"
	@echo "    theorems           - List key proven theorems"
	@echo "    holes              - Find unfinished proofs ({!!})"
	@echo "    search PATTERN=x   - Search for pattern in all files"
	@echo "    loc                - Count lines of code"
	@echo ""
	@echo "  Maintenance:"
	@echo "    clean              - Remove generated .agdai files"
	@echo "    help               - Show this help"
