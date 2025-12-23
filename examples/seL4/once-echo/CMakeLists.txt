#
# Once Echo Server for seL4
#
# A minimal seL4 application that demonstrates Once-compiled code
# running as a seL4 rootserver.
#

cmake_minimum_required(VERSION 3.16.0)

project(once-echo C)

# Find required seL4 packages
find_package(musllibc REQUIRED)
find_package(util_libs REQUIRED)
find_package(seL4_libs REQUIRED)

# Setup build environment with musl libc and sel4runtime
musllibc_setup_build_environment_with_sel4runtime()
sel4_import_libsel4()
util_libs_import_libraries()
sel4_libs_import_libraries()

# Source files
file(GLOB sources src/*.c)

# Create executable
add_executable(once-echo EXCLUDE_FROM_ALL ${sources})

target_include_directories(once-echo PRIVATE "include")

target_link_libraries(
    once-echo
    PUBLIC
        sel4_autoconf
        muslc
        sel4
        sel4runtime
        sel4allocman
        sel4vka
        sel4utils
        sel4platsupport
        sel4muslcsys
)

target_compile_options(once-echo PRIVATE -Werror -g)

# Declare as rootserver
include(rootserver)
DeclareRootserver(once-echo)
