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
X86_FOUNDATION := Once/Backend/X86/Correct/Foundation.agda
X86_SEQHELPERS := Once/Backend/X86/Correct/SequenceHelpers.agda
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

# Agda command: discovers standard library path from Nix store
# The library file is created dynamically to avoid hardcoded paths
define AGDA_CMD
STD_LIB=$$(find /nix/store -maxdepth 2 -name "standard-library.agda-lib" 2>/dev/null | head -1); \
if [ -z "$$STD_LIB" ]; then echo "Error: standard-library not found in Nix store"; exit 1; fi; \
AGDA_DIR="" agda --library-file=<(echo "$$STD_LIB"; echo "Once.agda-lib")
endef

.PHONY: all check postulates laws surface surfaceir optimize common x86 x86-correct x86-foundation aarch64 aarch64-correct aarch64-foundation riscv riscv-correct riscv-foundation endtoend endtoend-aarch64 primitives spf malonzo emit malonzo-codegen clean

all: check

check: postulates laws surface surfaceir optimize common x86 aarch64 endtoend endtoend-aarch64 primitives spf
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

common:
	@echo "Type-checking common backend lemmas..."
	@nix develop ..#default --command sh -c '$(AGDA_CMD) $(COMMON_FETCH)'
	@nix develop ..#default --command sh -c '$(AGDA_CMD) $(COMMON_EXEC)'
	@nix develop ..#default --command sh -c '$(AGDA_CMD) $(COMMON_MEMORY)'

x86:
	@echo "Type-checking x86-64 backend..."
	@nix develop ..#default --command sh -c '$(AGDA_CMD) $(X86_SYNTAX)'
	@nix develop ..#default --command sh -c '$(AGDA_CMD) $(X86_SEMANTICS)'
	@nix develop ..#default --command sh -c '$(AGDA_CMD) $(X86_CODEGEN)'
	@nix develop ..#default --command sh -c '$(AGDA_CMD) $(X86_CORRECT)'

x86-correct:
	@echo "Type-checking x86-64 correctness proofs only..."
	@nix develop ..#default --command sh -c '$(AGDA_CMD) $(X86_CORRECT)'

x86-foundation:
	@echo "Type-checking x86-64 foundation module only..."
	@nix develop ..#default --command sh -c '$(AGDA_CMD) $(X86_FOUNDATION)'

aarch64:
	@echo "Type-checking AArch64 backend..."
	@nix develop ..#default --command sh -c '$(AGDA_CMD) $(AARCH64_SYNTAX)'
	@nix develop ..#default --command sh -c '$(AGDA_CMD) $(AARCH64_SEMANTICS)'
	@nix develop ..#default --command sh -c '$(AGDA_CMD) $(AARCH64_CODEGEN)'
	@nix develop ..#default --command sh -c '$(AGDA_CMD) $(AARCH64_CORRECT)'

aarch64-correct:
	@echo "Type-checking AArch64 correctness proofs only..."
	@nix develop ..#default --command sh -c '$(AGDA_CMD) $(AARCH64_CORRECT)'

aarch64-foundation:
	@echo "Type-checking AArch64 foundation module only..."
	@nix develop ..#default --command sh -c '$(AGDA_CMD) $(AARCH64_FOUNDATION)'

riscv:
	@echo "Type-checking RISC-V 64-bit backend..."
	@nix develop ..#default --command sh -c '$(AGDA_CMD) $(RISCV_SYNTAX)'
	@if [ -f "$(RISCV_SEMANTICS)" ]; then nix develop ..#default --command sh -c '$(AGDA_CMD) $(RISCV_SEMANTICS)'; fi
	@if [ -f "$(RISCV_CODEGEN)" ]; then nix develop ..#default --command sh -c '$(AGDA_CMD) $(RISCV_CODEGEN)'; fi
	@if [ -f "$(RISCV_CORRECT)" ]; then nix develop ..#default --command sh -c '$(AGDA_CMD) $(RISCV_CORRECT)'; fi

riscv-correct:
	@echo "Type-checking RISC-V correctness proofs only..."
	@if [ -f "$(RISCV_CORRECT)" ]; then nix develop ..#default --command sh -c '$(AGDA_CMD) $(RISCV_CORRECT)'; fi

riscv-foundation:
	@echo "Type-checking RISC-V foundation module only..."
	@nix develop ..#default --command sh -c '$(AGDA_CMD) $(RISCV_FOUNDATION)'

endtoend:
	@echo "Type-checking end-to-end compilation theorem (x86)..."
	@nix develop ..#default --command sh -c '$(AGDA_CMD) $(ENDTOEND)'

endtoend-aarch64:
	@echo "Type-checking end-to-end compilation theorem (AArch64)..."
	@nix develop ..#default --command sh -c '$(AGDA_CMD) $(ENDTOEND_AARCH64)'

primitives:
	@echo "Type-checking primitive specifications..."
	@nix develop ..#default --command sh -c '$(AGDA_CMD) $(PRIM_MEMORY)'
	@nix develop ..#default --command sh -c '$(AGDA_CMD) $(PRIM_IO)'
	@nix develop ..#default --command sh -c '$(AGDA_CMD) $(PRIM_THREAD)'

spf:
	@echo "Type-checking strictly positive functors..."
	@nix develop ..#default --command sh -c '$(AGDA_CMD) $(SPF)'

malonzo:
	@echo "Generating Haskell via MAlonzo..."
	@mkdir -p _build/malonzo
	@nix develop ..#default --command sh -c '$(AGDA_CMD) -c --ghc-dont-call-ghc --compile-dir=_build/malonzo $(COMPILE)'
	@echo "Generated Haskell files in _build/malonzo/"
	@echo "Entry point: MAlonzo.Code.Once.Compile"

emit:
	@echo "Type-checking assembly emission modules..."
	@nix develop ..#default --command sh -c '$(AGDA_CMD) $(AARCH64_EMIT)'
	@nix develop ..#default --command sh -c '$(AGDA_CMD) $(X86_EMIT)'
	@nix develop ..#default --command sh -c '$(AGDA_CMD) $(RISCV_EMIT)'
	@nix develop ..#default --command sh -c '$(AGDA_CMD) $(EMIT_ALL)'

malonzo-codegen:
	@echo "Extracting verified code generators via MAlonzo..."
	@mkdir -p _build/malonzo
	@nix develop ..#default --command sh -c '$(AGDA_CMD) -c --ghc-dont-call-ghc --compile-dir=_build/malonzo $(EMIT_ALL)'
	@echo "Copying MAlonzo files to compiler..."
	@mkdir -p ../compiler/src/MAlonzo/Code/Once/Backend
	@cp -r _build/malonzo/MAlonzo/Code/Once/Backend/* ../compiler/src/MAlonzo/Code/Once/Backend/
	@echo "  - Backend modules copied"
	@# Copy core dependencies (IR, Type) that Backend modules need
	@cp _build/malonzo/MAlonzo/Code/Once/IR.hs ../compiler/src/MAlonzo/Code/Once/ 2>/dev/null || true
	@cp _build/malonzo/MAlonzo/Code/Once/Type.hs ../compiler/src/MAlonzo/Code/Once/ 2>/dev/null || true
	@echo "  - Core IR/Type modules copied"
	@echo "Done. Verified code generators in compiler/src/MAlonzo/Code/Once/Backend/"

clean:
	rm -rf _build
	find . -name "*.agdai" -delete
