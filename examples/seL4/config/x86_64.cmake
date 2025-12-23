# CMake Toolchain for seL4 x86_64

set(CMAKE_SYSTEM_NAME Generic)
set(CMAKE_SYSTEM_PROCESSOR x86_64)

# Compilers (native for x86_64-linux)
set(CMAKE_C_COMPILER gcc)
set(CMAKE_CXX_COMPILER g++)
set(CMAKE_ASM_COMPILER gcc)

# Compiler flags for bare-metal seL4
set(CMAKE_C_FLAGS_INIT "-nostdlib -ffreestanding -m64 -mno-red-zone")
set(CMAKE_CXX_FLAGS_INIT "-nostdlib -ffreestanding -m64 -mno-red-zone -fno-exceptions -fno-rtti")
set(CMAKE_ASM_FLAGS_INIT "-m64")

# Linker flags
set(CMAKE_EXE_LINKER_FLAGS_INIT "-nostdlib -Wl,--gc-sections -m64")

# Don't search for programs in the target environment
set(CMAKE_FIND_ROOT_PATH_MODE_PROGRAM NEVER)

# Search for libraries and headers in the target environment
set(CMAKE_FIND_ROOT_PATH_MODE_LIBRARY ONLY)
set(CMAKE_FIND_ROOT_PATH_MODE_INCLUDE ONLY)

# seL4 platform
set(PLATFORM "x86_64" CACHE STRING "seL4 platform")
set(KernelArch "x86" CACHE STRING "Kernel architecture")
set(KernelX86Sel4Arch "x86_64" CACHE STRING "seL4 architecture")
