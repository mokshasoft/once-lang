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
#   make ccc-x86v3    - CCC code gen for X86v3
#   make arith-x86v3  - Arithmetic primitives for X86v3
#   make compiler-x86v3 - Full X86v3 compiler
#
# Dead code analysis (requires patched Agda):
#   make dead-code-ccc-x86v3 - Dead code analysis for X86v3 CCC
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
all: compiler
	@echo "All proofs type-check successfully!"

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
# Pipeline: CCC Backend (target-specific)
#-----------------------------------------------------------------------------

.PHONY: ccc-x86v3
ccc-x86v3:
	@echo "Type-checking X86v3 CCC backend..."
	@sh -c '$(AGDA_CMD) Once/CCC/Target/X86v3/WholeProgram.agda'

#-----------------------------------------------------------------------------
# Pipeline: Arithmetic Primitives (target-specific)
#-----------------------------------------------------------------------------

.PHONY: arith-x86v3
arith-x86v3:
	@echo "Type-checking X86v3 arithmetic primitives..."
	@sh -c '$(AGDA_CMD) Once/Arith/Target/X86v3/PrimProofs.agda'

#-----------------------------------------------------------------------------
# Full Compiler (frontend + target)
#-----------------------------------------------------------------------------

.PHONY: compiler-x86v3
compiler-x86v3: frontend ccc-x86v3 arith-x86v3
	@echo "X86v3 compiler proofs type-check successfully!"

.PHONY: compiler
compiler: compiler-x86v3
	@echo "All compiler proofs type-check successfully!"

#-----------------------------------------------------------------------------
# MAlonzo Extraction
#-----------------------------------------------------------------------------

.PHONY: malonzo
malonzo:
	@echo "Extracting compiler via MAlonzo..."
	@mkdir -p _build/malonzo
	@sh -c '$(AGDA_CMD) -c --ghc-dont-call-ghc --compile-dir=_build/malonzo Once/Compile.agda'
	@echo "Copying extracted modules to compiler..."
	@rm -rf ../compiler/src/MAlonzo/Code/Once
	@mkdir -p ../compiler/src/MAlonzo/Code/Once
	@cp -r _build/malonzo/MAlonzo/Code/Once/* ../compiler/src/MAlonzo/Code/Once/
	@echo "Done! MAlonzo modules extracted to compiler/src/MAlonzo/Code/Once/"

#-----------------------------------------------------------------------------
# Dead Code Analysis (requires patched Agda with --dead-code)
#-----------------------------------------------------------------------------

.PHONY: dead-code-ccc-x86v3
dead-code-ccc-x86v3:
	@echo "Running dead code analysis on X86v3 CCC..."
	@./run-dead-code.sh Once.CCC.Target.X86v3.WholeProgram.compile-correct Once/CCC/Target/X86v3/WholeProgram.agda

#-----------------------------------------------------------------------------
# Utilities
#-----------------------------------------------------------------------------

.PHONY: agda
agda:
	@if [ -z "$(MODULE)" ]; then echo "Usage: make agda MODULE=Once/Path/To/File.agda"; exit 1; fi
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
