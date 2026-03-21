# Makefile for the Once bootstrap normalizer verification
#
# Run from bootstrap/ directory: make -C normalizer
# Or from normalizer/ directory with: cd .. && agda normalizer/MainTheorem.agda

AGDA := cd .. && agda
AGDA_FILES := $(shell find . -name "*.agda")

.PHONY: all check check-main postulates postulates-summary clean help

# Default: type-check the main theorem
all: check-main

# Type-check the main theorem (pulls in all dependencies)
check-main:
	$(AGDA) normalizer/MainTheorem.agda

# Type-check all Agda files individually
check:
	@echo "Type-checking all Agda files..."
	@for f in $(AGDA_FILES); do \
		echo "Checking $$f"; \
		(cd .. && agda "normalizer/$$f") || exit 1; \
	done
	@echo "All files type-check successfully."

# Check specific modules
check-foundations:
	$(AGDA) normalizer/Foundations/CCC.agda
	$(AGDA) normalizer/Foundations/Encoding.agda
	$(AGDA) normalizer/Foundations/Confluence.agda

check-correctness:
	$(AGDA) normalizer/Correctness/Correctness.agda

check-implementation:
	$(AGDA) normalizer/Implementation/Normalizer.agda

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
	@echo "  all                - Type-check main theorem (default)"
	@echo "  check-main         - Type-check MainTheorem.agda (full verification)"
	@echo "  check              - Type-check all Agda files individually"
	@echo "  check-foundations  - Check only Foundations modules"
	@echo "  check-correctness  - Check Correctness module"
	@echo "  check-implementation - Check Implementation/Normalizer"
	@echo "  postulates-quick   - Quick grep for postulate blocks"
	@echo "  postulates         - List all postulates with their types"
	@echo "  postulates-summary - Summary count of postulates per file"
	@echo "  theorems           - List key proven theorems"
	@echo "  holes              - Find unfinished proofs ({!!})"
	@echo "  search PATTERN=x   - Search for pattern in all files"
	@echo "  loc                - Count lines of code"
	@echo "  clean              - Remove generated .agdai files"
	@echo "  help               - Show this help"
