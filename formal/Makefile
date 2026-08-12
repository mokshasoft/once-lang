# Makefile for Once formal verification (Agda proofs)
#
# PREREQUISITE: Run from within 'nix develop' shell (from repo root).
#
# Full compiler:
#   make              - Build all targets (same as 'make compiler')
#   make compiler     - Build all targets
#
# Pipeline steps (target-independent):
#   make frontend     - Parse → TypeCheck → Elaborate → Desugar → Optimize → Escape → Fusion
#   make parser       - Parser
#   make typecheck    - Verified type checker
#   make elaborate    - Surface → IR elaboration
#   make desugar      - Desugaring
#   make optimize     - Optimizer
#   make escape       - Escape analysis
#   make fusion       - Fusion/deforestation
#
# Standalone proofs (not part of compilation pipeline):
#   make postulates   - Core postulates (pulled in automatically)
#   make laws         - Categorical laws + type soundness
#   make spf          - Strictly positive functors
#
# Target-specific steps (step-target):
#   make ccc-x86-64    - CCC code gen for X86-64
#   make arith-x86-64  - Arithmetic primitives for X86-64
#   make compiler      - Verify the whole compiler (= certified; apex + bundle)
#   make certified     - Correctness (CorrectCompiler) AND VerifiedTypeChecker
#   make check-all     - Type-check EVERY module (island-rot backstop)
#
# Dead code analysis (requires patched Agda):
#   make dead-code-ccc-x86-64 - Dead code analysis for X86-64 CCC
#
# Utilities:
#   make agda MODULE=path  - Type-check single module
#   make malonzo           - Extract compiler to Haskell
#   make clean             - Remove build artifacts

#-----------------------------------------------------------------------------
# Agda command setup
#-----------------------------------------------------------------------------

define AGDA_CMD
STD_LIB=$$(find /nix/store -maxdepth 2 -name "standard-library.agda-lib" 2>/dev/null | head -1); \
if [ -z "$$STD_LIB" ]; then echo "Error: standard-library not found in Nix store"; exit 1; fi; \
unset AGDA_DIR; agda --library-file=<(echo "$$STD_LIB"; echo "Once.agda-lib")
endef

#-----------------------------------------------------------------------------
# Default target
#-----------------------------------------------------------------------------

.PHONY: all
all: certified

#-----------------------------------------------------------------------------
# Pipeline: Frontend (target-independent)
#-----------------------------------------------------------------------------

.PHONY: parser
parser:
	@echo "Type-checking parser..."
	@sh -c '$(AGDA_CMD) Once/Parser.agda'

.PHONY: typecheck
typecheck:
	@echo "Type-checking verified type checker..."
	@sh -c '$(AGDA_CMD) Once/TypeCheck.agda'

# The SHIPPED artefact: correctness (Once.Adequacy.CorrectCompiler) CONJOINED
# with the well-behavedness bundle (Once.TypeCheck.Verified — determinism,
# totality, error-preservation, frontend identities). A single entry that gates
# BOTH; a regression in either fails this target. See Once/Certified.agda.
.PHONY: certified
certified:
	@echo "Type-checking the certified artefact (correctness AND well-behavedness)..."
	@sh -c '$(AGDA_CMD) Once/Certified.agda'

# Island-rot backstop: type-check EVERY module (not just the apex closure), so an
# off-apex proof can never rot silently again (as ErrorProofs did). Generates a
# transient Everything module importing the whole tree. Heavy — CI / on demand.
.PHONY: check-all
check-all:
	@echo "module Everything where" > Everything.agda
	@find Once -name '*.agda' | LC_ALL=C sort | sed 's|/|.|g; s|\.agda$$||; s|^|import |' >> Everything.agda
	@sh -c '$(AGDA_CMD) Everything.agda'; status=$$?; rm -f Everything.agda Everything.agdai; exit $$status

.PHONY: elaborate
elaborate:
	@echo "Type-checking elaboration (Surface → IR)..."
	@sh -c '$(AGDA_CMD) Once/Surface/Correct.agda'

.PHONY: desugar
desugar:
	@echo "Type-checking desugaring..."
	@sh -c '$(AGDA_CMD) Once/Surface/Desugar/Correct.agda'

.PHONY: optimize
optimize:
	@echo "Type-checking optimizer..."
	@sh -c '$(AGDA_CMD) Once/Optimize/Correct.agda'

.PHONY: escape
escape:
	@echo "Type-checking escape analysis..."
	@sh -c '$(AGDA_CMD) Once/Escape/Correct.agda'

.PHONY: fusion
fusion:
	@echo "Type-checking fusion/deforestation..."
	@sh -c '$(AGDA_CMD) Once/Fusion/Correct.agda'

.PHONY: frontend
frontend: parser typecheck elaborate desugar optimize escape fusion
	@echo "Frontend proofs type-check successfully!"

#-----------------------------------------------------------------------------
# Standalone proofs (not part of compilation pipeline)
#-----------------------------------------------------------------------------

.PHONY: postulates
postulates:
	@echo "Type-checking postulates..."
	@sh -c '$(AGDA_CMD) Once/Postulates.agda'

.PHONY: laws
laws:
	@echo "Type-checking categorical laws..."
	@sh -c '$(AGDA_CMD) Once/Category/Laws.agda'
	@sh -c '$(AGDA_CMD) Once/TypeSystem/Soundness.agda'

.PHONY: spf
spf:
	@echo "Type-checking strictly positive functors..."
	@sh -c '$(AGDA_CMD) Once/SPF.agda'

#-----------------------------------------------------------------------------
# Optimizer Completeness Proofs (separate from compiler)
#-----------------------------------------------------------------------------

.PHONY: optimizer-cost
optimizer-cost:
	@echo "Type-checking optimizer cost model..."
	@sh -c '$(AGDA_CMD) Once/Optimizer/Cost.agda'

.PHONY: optimizer-depth
optimizer-depth:
	@echo "Type-checking optimizer depth..."
	@sh -c '$(AGDA_CMD) Once/Optimizer/Depth.agda'

.PHONY: optimizer-rewrite
optimizer-rewrite:
	@echo "Type-checking optimizer rewrite relation..."
	@sh -c '$(AGDA_CMD) Once/Optimizer/Rewrite.agda'

.PHONY: optimizer-complete
optimizer-complete:
	@echo "Type-checking optimizer completeness..."
	@sh -c '$(AGDA_CMD) Once/Optimizer/Complete.agda'

.PHONY: optimizer-bcc
optimizer-bcc:
	@echo "Type-checking BCC completeness..."
	@sh -c '$(AGDA_CMD) Once/Optimizer/BCC.agda'

.PHONY: optimizer
optimizer: optimizer-cost optimizer-depth optimizer-rewrite optimizer-complete optimizer-bcc
	@echo "Optimizer completeness proofs type-check successfully!"

#-----------------------------------------------------------------------------
# Pipeline: CCC Backend (target-specific)
#-----------------------------------------------------------------------------

.PHONY: ccc-x86-64
ccc-x86-64:
	@echo "Type-checking X86-64 CCC backend (Target instance)..."
	@sh -c '$(AGDA_CMD) Once/Target/X86-64.agda'

.PHONY: ccc-x86-32
ccc-x86-32:
	@echo "Type-checking X86-32 CCC backend (Target instance)..."
	@sh -c '$(AGDA_CMD) Once/Target/X86-32.agda'

.PHONY: ccc-riscv64
ccc-riscv64:
	@echo "Type-checking RISC-V 64 CCC backend (Target instance)..."
	@sh -c '$(AGDA_CMD) Once/Target/RiscV64.agda'
# Plan 0.65: the riscv64 SECOND INSTANCE of the arch-generic correspondence
# core. `Once/Target/RiscV64.agda` is the emitter and does not import these, so
# without naming them here they would be islands — green when checked by hand
# and invisible to the gate, which is the one failure mode a second instance
# exists to prevent.
	@sh -c '$(AGDA_CMD) Once/Adequacy/ArchCorrectness/RiscV64/RegRoles.agda'
	@sh -c '$(AGDA_CMD) Once/Adequacy/ArchCorrectness/RiscV64/FlatComposition.agda'
	@sh -c '$(AGDA_CMD) Once/Adequacy/ArchCorrectness/RiscV64/FlatCorrespondence.agda'

#-----------------------------------------------------------------------------
# Pipeline: Arithmetic Primitives (target-specific)
#-----------------------------------------------------------------------------

.PHONY: arith-x86-64
arith-x86-64:
	@echo "Type-checking X86-64 arithmetic primitives..."
	@sh -c '$(AGDA_CMD) Once/Arith/SigOp/Proofs.agda'

#-----------------------------------------------------------------------------
# Full Compiler (frontend + target)
#-----------------------------------------------------------------------------

.PHONY: compiler-x86-32
compiler-x86-32: frontend ccc-x86-32
	@echo "X86-32 compiler proofs type-check successfully!"

.PHONY: compiler-riscv64
compiler-riscv64: frontend ccc-riscv64
	@echo "RISC-V 64 compiler proofs type-check successfully!"

# The apex verification is `certified` (Once.Certified — the arch-generic
# `CorrectCompiler` proof for every target via `arch-correctness`, conjoined
# with the `VerifiedTypeChecker` bundle). The former `Once/Compile/EndToEnd.agda`
# single-entry target was removed: that module no longer exists.
.PHONY: compiler
compiler: certified
	@echo "Compiler verified (correctness + well-behavedness)!"

.PHONY: compiler-all
compiler-all: certified compiler-x86-32 compiler-riscv64
	@echo "All-arch compiler proofs type-check successfully!"

#-----------------------------------------------------------------------------
# MAlonzo Extraction
#-----------------------------------------------------------------------------

.PHONY: malonzo
malonzo:
	@if [ -z "$$AGDA_SAFE_ACTIVE" ] && [ -z "$$AGDA_SAFE_DISABLE" ]; then \
	  exec $(CURDIR)/scripts/agda-safe.sh malonzo; \
	fi
	@echo "Extracting compiler via MAlonzo..."
	@mkdir -p _build/malonzo
	@# Extract from Once/Compiler.agda (the verified instance) which
	@# transitively reaches Once.Compile + the Verified hierarchy. Bridge.hs
	@# imports the verified entry point from this extraction.
	@sh -c '$(AGDA_CMD) -c --ghc-dont-call-ghc --compile-dir=_build/malonzo Once/Compiler.agda'
	@echo "Copying extracted modules to compiler..."
	@rm -rf ../compiler/src/MAlonzo/Code/Once
	@mkdir -p ../compiler/src/MAlonzo/Code/Once
	@cp -r _build/malonzo/MAlonzo/Code/Once/* ../compiler/src/MAlonzo/Code/Once/
	@echo "Done! MAlonzo modules extracted to compiler/src/MAlonzo/Code/Once/"

#-----------------------------------------------------------------------------
# Dead Code Analysis (requires patched Agda with --dead-code)
#-----------------------------------------------------------------------------

.PHONY: dead-code-ccc-x86-64
dead-code-ccc-x86-64:
	@echo "Running dead code analysis on X86-64 (Adequacy apex)..."
	@./run-dead-code.sh Once.Adequacy.ArchCorrectness.X86-64.x86-64-correct Once/Adequacy/ArchCorrectness/X86-64.agda

#-----------------------------------------------------------------------------
# Postulate Detection
#-----------------------------------------------------------------------------

# Patched Agda command (for --warn-postulates)
# Uses local writable stdlib cache for interface files
PATCHED_AGDA := $(shell ls -t /home/whatever/Repo/OpenSource/agda/dist-newstyle/build/x86-64-linux/ghc-*/Agda-2.8.0/x/agda/build/agda/agda 2>/dev/null | head -1)
LOCAL_STD_LIB_DIR := $(HOME)/_stdlib-cache

define PATCHED_AGDA_CMD
if [ ! -f "$(LOCAL_STD_LIB_DIR)/standard-library.agda-lib" ]; then \
  NIX_STD_LIB_DIR=$$(dirname $$(find /nix/store -maxdepth 2 -name "standard-library.agda-lib" 2>/dev/null | head -1)); \
  echo "Creating local writable copy of stdlib..."; \
  mkdir -p "$(LOCAL_STD_LIB_DIR)"; \
  cp -r "$$NIX_STD_LIB_DIR"/* "$(LOCAL_STD_LIB_DIR)"/; \
  chmod -R u+w "$(LOCAL_STD_LIB_DIR)"; \
fi; \
unset AGDA_DIR; export LC_ALL=en_US.utf8; $(PATCHED_AGDA) --library-file=<(echo "$(LOCAL_STD_LIB_DIR)/standard-library.agda-lib"; echo "Once.agda-lib") --transliterate --warn-postulates
endef

# Fast grep scan for postulates
.PHONY: postulates-grep
postulates-grep:
	@echo "Scanning for postulates (grep)..."
	@grep -rn "^postulate$$\|^postulate $$" --include="*.agda" Once/ || echo "No postulates found."
	@grep -rn "^ *postulate$$\|^ *postulate " --include="*.agda" Once/ || true

# Audit surface for `{-# CATCHALL #-}` pragmas (plan 0.9).
# Each marker silences a CoverageNoExactSplit warning on a deliberate
# catch-all. Treat this list the way `make postulates-grep` is treated:
# small, finite, every entry justified.
.PHONY: catchalls
catchalls:
	@echo "Scanning for {-# CATCHALL #-} pragmas..."
	@grep -rn "{-# CATCHALL #-}" --include="*.agda" Once/ | sort || echo "No CATCHALL pragmas found."

# Census of remaining CoverageNoExactSplit warning sites (plan 0.9
# discipline backlog — not promoted to error yet). Each site is a
# catch-all that hasn't been refactored to exhaustive enumeration or
# explicitly marked CATCHALL. None are in the bug-hiding class
# (silent state-mutation absorption); those were closed in phases B
# and D. Run after a fresh build; reads from $(CENSUS_LOG).
CENSUS_LOG ?= /tmp/once-exact-split-census.log
.PHONY: exact-split-census
exact-split-census:
	@echo "Building with --exact-split warnings → $(CENSUS_LOG)..."
	@$(MAKE) compiler 2>&1 | tee $(CENSUS_LOG) > /dev/null || true
	@echo "Unique CoverageNoExactSplit sites:"
	@grep "warning: -W\[no\]CoverageNoExactSplit" $(CENSUS_LOG) | \
	  sed 's|.*formal/||; s|: warning.*||' | sort -u | tee /dev/stderr | wc -l

# Precise postulate detection using patched Agda (X86-64 CCC: Dispatcher + Refinement + CodeGen)
.PHONY: postulates-ccc-x86-64
postulates-ccc-x86-64:
	@echo "Checking postulates in X86-64 CCC (Target instance)..."
	@sh -c '$(PATCHED_AGDA_CMD) --warn-postulates Once/Target/X86-64.agda'

# Precise postulate detection using patched Agda (X86-64 Arith)
.PHONY: postulates-arith-x86-64
postulates-arith-x86-64:
	@echo "Checking postulates in X86-64 Arith (precise)..."
	@sh -c '$(PATCHED_AGDA_CMD) --warn-postulates Once/Arith/SigOp/Proofs.agda'

# Precise postulate detection for full X86-64 compiler
.PHONY: postulates-x86-64
postulates-x86-64: postulates-ccc-x86-64 postulates-arith-x86-64
	@echo "Postulate check complete for X86-64."

#-----------------------------------------------------------------------------
# Denotational-semantics TP-cleanliness gate (D062)
#-----------------------------------------------------------------------------

# Fast iteration tracker (grep only, no Agda run): scans the denotational
# meaning's transitive import closure for TERMINATING / trustMe / --sized-types
# / postulate. Pass roots as args; default = the semantic core (evalᴰ + ⟦_⟧ˢ).
# NOTE: this is import-closure, a CONSERVATIVE over-approximation of the
# use-chain — it also surfaces in-closure-but-unused pragmas (e.g. the abstract
# machine's exec-loop, pulled via CCC.IR). GREEN ⟹ definitely TP-clean.
.PHONY: denot-audit
denot-audit:
	@bash scripts/denot-audit.sh

# The denotational TP gate (D062). GREEN ⟹ the meaning's import closure is free
# of the escape hatches that would break totality/productivity: TERMINATING /
# NON_TERMINATING / primTrustMe / --sized-types. This is the right gate because
# the meaning legitimately RESTS ON two declared extensionality axioms — `funext`
# (function extensionality) and `bisimS-to-eq` (coalgebraic extensionality,
# bisimilar ⟹ equal) — which are valid (Cubical-provable) but which a raw `agda
# --safe` rejects outright (`--safe` forbids ALL postulates). So the gate is the
# escape-hatch audit, not `--safe`. (Postulate-level cleanliness — discharging
# the SigOp/arith value contracts and parameterising over the two axioms — is the
# stricter `denot-safe-strict` target below, intentionally axiom-blocked.)
.PHONY: denot-safe
denot-safe:
	@bash scripts/denot-audit.sh

# Stricter aspirational check: the REAL meaning module under `agda --safe`. This
# additionally rejects incomplete patterns / unsolved metas / any unsafe pragma —
# but is BLOCKED (by design, not by a gap) on the accepted axioms `funext` /
# `bisimS-to-eq` and the deferred SigOp/arith value contracts. Not expected green
# until those are parameterised away / discharged. Run to see the residual list.
.PHONY: denot-safe-strict
denot-safe-strict:
	@if [ -z "$$AGDA_SAFE_ACTIVE" ] && [ -z "$$AGDA_SAFE_DISABLE" ]; then \
	  exec $(CURDIR)/scripts/agda-safe.sh denot-safe-strict; \
	fi
	@echo "Type-checking the denotational meaning (Once.Denotation.DenotTrace) under --safe..."
	@sh -c '$(AGDA_CMD) --safe Once.Denotation.DenotTrace.agda'

#-----------------------------------------------------------------------------
# Utilities
#-----------------------------------------------------------------------------

# `make agda` and `make malonzo` are the heaviest targets and can OOM
# the box (see scripts/agda-safe.sh for context). When invoked directly
# (AGDA_SAFE_ACTIVE unset), they re-exec themselves through the
# cgroup-based safety wrapper so a runaway type-check can only kill its
# own subtree — not the claude-code harness. The wrapper exports
# AGDA_SAFE_ACTIVE=1 to break the recursion. Set AGDA_SAFE_DISABLE=1 to
# opt out (e.g. on CI with its own memory controls).
.PHONY: agda
agda:
	@if [ -z "$(MODULE)" ]; then echo "Usage: make agda MODULE=Once/Path/To/File.agda"; exit 1; fi
	@if [ -z "$$AGDA_SAFE_ACTIVE" ] && [ -z "$$AGDA_SAFE_DISABLE" ]; then \
	  exec $(CURDIR)/scripts/agda-safe.sh agda MODULE=$(MODULE); \
	fi
	@echo "Type-checking $(MODULE)..."
	@sh -c '$(AGDA_CMD) $(MODULE)'

.PHONY: clean
clean:
	rm -rf _build
	find . -name "*.agdai" -delete

#-----------------------------------------------------------------------------
# Legacy targets (other architectures - paths need updating)
#-----------------------------------------------------------------------------

# TODO: Add when needed:
#   ccc-x86, arith-x86, compiler-x86
#   ccc-aarch64, arith-aarch64, compiler-aarch64
#   ccc-riscv64, arith-riscv64, compiler-riscv64
