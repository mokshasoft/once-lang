# Makefile for Once formal verification (Agda proofs)
#
# This Makefile runs Agda type-checking within the nix develop shell.
# The standard library path is discovered dynamically from the Nix environment.
#
# Usage:
#   make          - Type-check all Agda files
#   make check    - Same as above
#   make laws     - Type-check categorical laws only
#   make surface  - Type-check surface syntax elaboration only
#   make surfaceir - Type-check surface IR and desugar (D035)
#   make optimize - Type-check optimizer correctness proofs
#   make clean    - Remove Agda build artifacts

# Main entry points for each module
POSTULATES := Once/Postulates.agda
LAWS := Once/Category/Laws.agda
SOUNDNESS := Once/TypeSystem/Soundness.agda
ELABORATE := Once/Surface/Elaborate.agda
CORRECT := Once/Surface/Correct.agda
SURFACE_IR := Once/Surface/IR.agda
SURFACE_DESUGAR := Once/Surface/Desugar.agda
SURFACE_DESUGAR_CORRECT := Once/Surface/Desugar/Correct.agda
OPTIMIZE := Once/Optimize.agda
OPTIMIZE_CORRECT := Once/Optimize/Correct.agda
X86_SYNTAX := Once/Backend/X86/Syntax.agda
X86_SEMANTICS := Once/Backend/X86/Semantics.agda
X86_CODEGEN := Once/Backend/X86/CodeGen.agda
X86_CORRECT := Once/Backend/X86/Correct.agda

# Agda command: discovers standard library path from Nix store
# The library file is created dynamically to avoid hardcoded paths
define AGDA_CMD
STD_LIB=$$(find /nix/store -maxdepth 2 -name "standard-library.agda-lib" 2>/dev/null | head -1); \
if [ -z "$$STD_LIB" ]; then echo "Error: standard-library not found in Nix store"; exit 1; fi; \
AGDA_DIR="" agda --library-file=<(echo "$$STD_LIB"; echo "Once.agda-lib")
endef

.PHONY: all check postulates laws surface surfaceir optimize x86 clean

all: check

check: postulates laws surface surfaceir optimize x86
	@echo "All proofs type-check successfully!"

postulates:
	@echo "Type-checking postulates..."
	@nix develop ..#default --command sh -c '$(AGDA_CMD) $(POSTULATES)'

laws:
	@echo "Type-checking categorical laws..."
	@nix develop ..#default --command sh -c '$(AGDA_CMD) $(LAWS)'
	@nix develop ..#default --command sh -c '$(AGDA_CMD) $(SOUNDNESS)'

surface:
	@echo "Type-checking surface syntax elaboration..."
	@nix develop ..#default --command sh -c '$(AGDA_CMD) $(ELABORATE)'
	@nix develop ..#default --command sh -c '$(AGDA_CMD) $(CORRECT)'

surfaceir:
	@echo "Type-checking surface IR and desugar..."
	@nix develop ..#default --command sh -c '$(AGDA_CMD) $(SURFACE_IR)'
	@nix develop ..#default --command sh -c '$(AGDA_CMD) $(SURFACE_DESUGAR)'
	@nix develop ..#default --command sh -c '$(AGDA_CMD) $(SURFACE_DESUGAR_CORRECT)'

optimize:
	@echo "Type-checking optimizer..."
	@nix develop ..#default --command sh -c '$(AGDA_CMD) $(OPTIMIZE)'
	@nix develop ..#default --command sh -c '$(AGDA_CMD) $(OPTIMIZE_CORRECT)'

x86:
	@echo "Type-checking x86-64 backend..."
	@nix develop ..#default --command sh -c '$(AGDA_CMD) $(X86_SYNTAX)'
	@nix develop ..#default --command sh -c '$(AGDA_CMD) $(X86_SEMANTICS)'
	@nix develop ..#default --command sh -c '$(AGDA_CMD) $(X86_CODEGEN)'
	@nix develop ..#default --command sh -c '$(AGDA_CMD) $(X86_CORRECT)'

clean:
	rm -rf _build
	find . -name "*.agdai" -delete
