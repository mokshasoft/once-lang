# CMake Toolchain for seL4 RISC-V 64-bit

set(CMAKE_SYSTEM_NAME Generic)
set(CMAKE_SYSTEM_PROCESSOR riscv64)

# Cross-compiler prefix
set(CROSS_COMPILER_PREFIX riscv64-none-elf-)

# Compilers
set(CMAKE_C_COMPILER ${CROSS_COMPILER_PREFIX}gcc)
set(CMAKE_CXX_COMPILER ${CROSS_COMPILER_PREFIX}g++)
set(CMAKE_ASM_COMPILER ${CROSS_COMPILER_PREFIX}gcc)

# Compiler flags for bare-metal seL4
set(CMAKE_C_FLAGS_INIT "-nostdlib -ffreestanding -march=rv64imac -mabi=lp64")
set(CMAKE_CXX_FLAGS_INIT "-nostdlib -ffreestanding -march=rv64imac -mabi=lp64 -fno-exceptions -fno-rtti")
set(CMAKE_ASM_FLAGS_INIT "-march=rv64imac -mabi=lp64")

# Linker flags
set(CMAKE_EXE_LINKER_FLAGS_INIT "-nostdlib -Wl,--gc-sections")

# Don't search for programs in the target environment
set(CMAKE_FIND_ROOT_PATH_MODE_PROGRAM NEVER)

# Search for libraries and headers in the target environment
set(CMAKE_FIND_ROOT_PATH_MODE_LIBRARY ONLY)
set(CMAKE_FIND_ROOT_PATH_MODE_INCLUDE ONLY)

# seL4 platform
set(PLATFORM "qemu-riscv-virt" CACHE STRING "seL4 platform")
set(KernelArch "riscv" CACHE STRING "Kernel architecture")
set(KernelRiscVSel4Arch "riscv64" CACHE STRING "seL4 architecture")
