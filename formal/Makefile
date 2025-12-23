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
#   make x86      - Type-check x86-64 backend proofs
#   make aarch64  - Type-check AArch64 backend proofs
#   make riscv    - Type-check RISC-V 64-bit backend proofs
#   make endtoend - Type-check end-to-end compilation theorem (x86)
#   make endtoend-aarch64 - Type-check end-to-end compilation theorem (AArch64)
#   make primitives - Type-check primitive specifications
#   make malonzo  - Generate Haskell via MAlonzo (D035)
#   make clean    - Remove Agda build artifacts
#   make agda MODULE=Once/Path/To/File.agda - Type-check a single module

# Main entry points for each module
POSTULATES := Once/Postulates.agda
LAWS := Once/Category/Laws.agda
SOUNDNESS := Once/TypeSystem/Soundness.agda
ELABORATE := Once/Surface/Elaborate.agda
CORRECT := Once/Surface/Correct.agda
SURFACE_IR := Once/Surface/IR.agda
SURFACE_DESUGAR := Once/Surface/Desugar.agda
SURFACE_DESUGAR_CORRECT := Once/Surface/Desugar/Correct.agda
COMPILE := Once/Compile.agda
OPTIMIZE := Once/Optimize.agda
OPTIMIZE_CORRECT := Once/Optimize/Correct.agda
X86_SYNTAX := Once/Backend/X86/Syntax.agda
X86_SEMANTICS := Once/Backend/X86/Semantics.agda
X86_CODEGEN := Once/Backend/X86/CodeGen.agda
X86_CORRECT := Once/Backend/X86/Correct.agda
X86_STAR := Once/Backend/X86/Correct/Star.agda
X86_STARBASE := Once/Backend/X86/Correct/StarBase.agda
X86_ENCODING := Once/Backend/X86/Encoding.agda
AARCH64_SYNTAX := Once/Backend/AArch64/Syntax.agda
AARCH64_SEMANTICS := Once/Backend/AArch64/Semantics.agda
AARCH64_CODEGEN := Once/Backend/AArch64/CodeGen.agda
AARCH64_CORRECT := Once/Backend/AArch64/Correct.agda
AARCH64_FOUNDATION := Once/Backend/AArch64/Correct/Foundation.agda
RISCV_SYNTAX := Once/Backend/RiscV64/Syntax.agda
RISCV_SEMANTICS := Once/Backend/RiscV64/Semantics.agda
RISCV_CODEGEN := Once/Backend/RiscV64/CodeGen.agda
RISCV_CORRECT := Once/Backend/RiscV64/Correct.agda
RISCV_FOUNDATION := Once/Backend/RiscV64/Correct/Foundation.agda
COMMON_FETCH := Once/Backend/Common/Fetch.agda
COMMON_EXEC := Once/Backend/Common/Exec.agda
COMMON_MEMORY := Once/Backend/Common/Memory.agda
AARCH64_EMIT := Once/Backend/AArch64/Emit.agda
X86_EMIT := Once/Backend/X86/Emit.agda
RISCV_EMIT := Once/Backend/RiscV64/Emit.agda
EMIT_ALL := Once/Backend/Emit.agda
ENDTOEND := Once/EndToEnd.agda
ENDTOEND_AARCH64 := Once/EndToEndAArch64.agda
PRIM_MEMORY := Once/Primitive/Memory.agda
PRIM_IO := Once/Primitive/IO.agda
PRIM_THREAD := Once/Primitive/Thread.agda
SPF := Once/SPF.agda

# Nix develop wrapper: suppress warnings and banner
NIX_DEVELOP := ONCE_QUIET=1 NIX_CONFIG="warn-dirty = false" nix --quiet develop '..\#agda' --command

# Agda command: discovers standard library path from Nix store
# The library file is created dynamically to avoid hardcoded paths
define AGDA_CMD
STD_LIB=$$(find /nix/store -maxdepth 2 -name "standard-library.agda-lib" 2>/dev/null | head -1); \
if [ -z "$$STD_LIB" ]; then echo "Error: standard-library not found in Nix store"; exit 1; fi; \
unset AGDA_DIR; agda --library-file=<(echo "$$STD_LIB"; echo "Once.agda-lib")
endef

.PHONY: all
all: check

.PHONY: check
check: postulates laws surface surfaceir optimize common x86 aarch64 endtoend endtoend-aarch64 primitives spf
	@echo "All proofs type-check successfully!"

.PHONY: postulates
postulates:
	@echo "Type-checking postulates..."
	@$(NIX_DEVELOP) sh -c '$(AGDA_CMD) $(POSTULATES)'

.PHONY: laws
laws:
	@echo "Type-checking categorical laws..."
	@$(NIX_DEVELOP) sh -c '$(AGDA_CMD) $(LAWS)'
	@$(NIX_DEVELOP) sh -c '$(AGDA_CMD) $(SOUNDNESS)'

.PHONY: surface
surface:
	@echo "Type-checking surface syntax elaboration..."
	@$(NIX_DEVELOP) sh -c '$(AGDA_CMD) $(ELABORATE)'
	@$(NIX_DEVELOP) sh -c '$(AGDA_CMD) $(CORRECT)'

.PHONY: surfaceir
surfaceir:
	@echo "Type-checking surface IR and desugar..."
	@$(NIX_DEVELOP) sh -c '$(AGDA_CMD) $(SURFACE_IR)'
	@$(NIX_DEVELOP) sh -c '$(AGDA_CMD) $(SURFACE_DESUGAR)'
	@$(NIX_DEVELOP) sh -c '$(AGDA_CMD) $(SURFACE_DESUGAR_CORRECT)'

.PHONY: optimize
optimize:
	@echo "Type-checking optimizer..."
	@$(NIX_DEVELOP) sh -c '$(AGDA_CMD) $(OPTIMIZE)'
	@$(NIX_DEVELOP) sh -c '$(AGDA_CMD) $(OPTIMIZE_CORRECT)'

.PHONY: common
common:
	@echo "Type-checking common backend lemmas..."
	@$(NIX_DEVELOP) sh -c '$(AGDA_CMD) $(COMMON_FETCH)'
	@$(NIX_DEVELOP) sh -c '$(AGDA_CMD) $(COMMON_EXEC)'
	@$(NIX_DEVELOP) sh -c '$(AGDA_CMD) $(COMMON_MEMORY)'

.PHONY: x86
x86:
	@echo "Type-checking x86-64 backend..."
	@$(NIX_DEVELOP) sh -c '$(AGDA_CMD) $(X86_SYNTAX)'
	@$(NIX_DEVELOP) sh -c '$(AGDA_CMD) $(X86_SEMANTICS)'
	@$(NIX_DEVELOP) sh -c '$(AGDA_CMD) $(X86_CODEGEN)'
	@$(NIX_DEVELOP) sh -c '$(AGDA_CMD) $(X86_CORRECT)'

.PHONY: x86-correct
x86-correct:
	@echo "Type-checking x86-64 correctness proofs only..."
	@$(NIX_DEVELOP) sh -c '$(AGDA_CMD) $(X86_CORRECT)'

.PHONY: x86-star
x86-star:
	@echo "Type-checking x86-64 star relation module..."
	@$(NIX_DEVELOP) sh -c '$(AGDA_CMD) $(X86_STAR)'

.PHONY: x86-starbase
x86-starbase:
	@echo "Type-checking x86-64 star base proofs..."
	@$(NIX_DEVELOP) sh -c '$(AGDA_CMD) $(X86_STARBASE)'

.PHONY: x86-encoding
x86-encoding:
	@echo "Type-checking x86-64 encoding derivations..."
	@$(NIX_DEVELOP) sh -c '$(AGDA_CMD) $(X86_ENCODING)'

.PHONY: aarch64
aarch64:
	@echo "Type-checking AArch64 backend..."
	@$(NIX_DEVELOP) sh -c '$(AGDA_CMD) $(AARCH64_SYNTAX)'
	@$(NIX_DEVELOP) sh -c '$(AGDA_CMD) $(AARCH64_SEMANTICS)'
	@$(NIX_DEVELOP) sh -c '$(AGDA_CMD) $(AARCH64_CODEGEN)'
	@$(NIX_DEVELOP) sh -c '$(AGDA_CMD) $(AARCH64_CORRECT)'

.PHONY: aarch64-correct
aarch64-correct:
	@echo "Type-checking AArch64 correctness proofs only..."
	@$(NIX_DEVELOP) sh -c '$(AGDA_CMD) $(AARCH64_CORRECT)'

.PHONY: aarch64-foundation
aarch64-foundation:
	@echo "Type-checking AArch64 foundation module only..."
	@$(NIX_DEVELOP) sh -c '$(AGDA_CMD) $(AARCH64_FOUNDATION)'

.PHONY: riscv
riscv:
	@echo "Type-checking RISC-V 64-bit backend..."
	@$(NIX_DEVELOP) sh -c '$(AGDA_CMD) $(RISCV_SYNTAX)'
	@if [ -f "$(RISCV_SEMANTICS)" ]; then $(NIX_DEVELOP) sh -c '$(AGDA_CMD) $(RISCV_SEMANTICS)'; fi
	@if [ -f "$(RISCV_CODEGEN)" ]; then $(NIX_DEVELOP) sh -c '$(AGDA_CMD) $(RISCV_CODEGEN)'; fi
	@if [ -f "$(RISCV_CORRECT)" ]; then $(NIX_DEVELOP) sh -c '$(AGDA_CMD) $(RISCV_CORRECT)'; fi

.PHONY: riscv-correct
riscv-correct:
	@echo "Type-checking RISC-V correctness proofs only..."
	@if [ -f "$(RISCV_CORRECT)" ]; then $(NIX_DEVELOP) sh -c '$(AGDA_CMD) $(RISCV_CORRECT)'; fi

.PHONY: riscv-foundation
riscv-foundation:
	@echo "Type-checking RISC-V foundation module only..."
	@$(NIX_DEVELOP) sh -c '$(AGDA_CMD) $(RISCV_FOUNDATION)'

.PHONY: endtoend
endtoend:
	@echo "Type-checking end-to-end compilation theorem (x86)..."
	@$(NIX_DEVELOP) sh -c '$(AGDA_CMD) $(ENDTOEND)'

.PHONY: endtoend-aarch64
endtoend-aarch64:
	@echo "Type-checking end-to-end compilation theorem (AArch64)..."
	@$(NIX_DEVELOP) sh -c '$(AGDA_CMD) $(ENDTOEND_AARCH64)'

.PHONY: primitives
primitives:
	@echo "Type-checking primitive specifications..."
	@$(NIX_DEVELOP) sh -c '$(AGDA_CMD) $(PRIM_MEMORY)'
	@$(NIX_DEVELOP) sh -c '$(AGDA_CMD) $(PRIM_IO)'
	@$(NIX_DEVELOP) sh -c '$(AGDA_CMD) $(PRIM_THREAD)'

.PHONY: spf
spf:
	@echo "Type-checking strictly positive functors..."
	@$(NIX_DEVELOP) sh -c '$(AGDA_CMD) $(SPF)'

.PHONY: malonzo
malonzo:
	@echo "Generating Haskell via MAlonzo..."
	@mkdir -p _build/malonzo
	@$(NIX_DEVELOP) sh -c '$(AGDA_CMD) -c --ghc-dont-call-ghc --compile-dir=_build/malonzo $(COMPILE)'
	@echo "Generated Haskell files in _build/malonzo/"
	@echo "Entry point: MAlonzo.Code.Once.Compile"

.PHONY: emit
emit:
	@echo "Type-checking assembly emission modules..."
	@$(NIX_DEVELOP) sh -c '$(AGDA_CMD) $(AARCH64_EMIT)'
	@$(NIX_DEVELOP) sh -c '$(AGDA_CMD) $(X86_EMIT)'
	@$(NIX_DEVELOP) sh -c '$(AGDA_CMD) $(RISCV_EMIT)'
	@$(NIX_DEVELOP) sh -c '$(AGDA_CMD) $(EMIT_ALL)'

.PHONY: malonzo-codegen
malonzo-codegen:
	@echo "Extracting verified code generators via MAlonzo..."
	@mkdir -p _build/malonzo
	@$(NIX_DEVELOP) sh -c '$(AGDA_CMD) -c --ghc-dont-call-ghc --compile-dir=_build/malonzo $(EMIT_ALL)'
	@echo "Copying MAlonzo files to compiler..."
	@mkdir -p ../compiler/src/MAlonzo/Code/Once/Backend
	@cp -r _build/malonzo/MAlonzo/Code/Once/Backend/* ../compiler/src/MAlonzo/Code/Once/Backend/
	@echo "  - Backend modules copied"
	@# Copy core dependencies (IR, Type) that Backend modules need
	@cp _build/malonzo/MAlonzo/Code/Once/IR.hs ../compiler/src/MAlonzo/Code/Once/ 2>/dev/null || true
	@cp _build/malonzo/MAlonzo/Code/Once/Type.hs ../compiler/src/MAlonzo/Code/Once/ 2>/dev/null || true
	@echo "  - Core IR/Type modules copied"
	@echo "Done. Verified code generators in compiler/src/MAlonzo/Code/Once/Backend/"

.PHONY: clean
clean:
	rm -rf _build
	find . -name "*.agdai" -delete

# Type-check a single Agda module
# Usage: make agda MODULE=Once/Path/To/File.agda
.PHONY: agda
agda:
	@if [ -z "$(MODULE)" ]; then echo "Usage: make agda MODULE=Once/Path/To/File.agda"; exit 1; fi
	@echo "Type-checking $(MODULE)..."
	@$(NIX_DEVELOP) sh -c '$(AGDA_CMD) $(MODULE)'
