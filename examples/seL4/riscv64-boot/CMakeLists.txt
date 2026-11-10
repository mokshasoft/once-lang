# SPDX-License-Identifier: AGPL-3.0-or-later
# Copyright (C) 2025-2026 Jonas Claesson
#
# On riscv64 the kernel and the root task boot together: seL4's elfloader
# holds both. This builds the kernel and the elfloader around an already
# linked Once image (`ONCE_IMAGE`). The paths are given by the flake.
cmake_minimum_required(VERSION 3.16.0)

list(APPEND CMAKE_MODULE_PATH
     "${SEL4_KERNEL}"
     "${SEL4_TOOLS}/cmake-tool/helpers"
     "${SEL4_TOOLS}/elfloader-tool")

project(once-sel4-riscv64-boot C ASM)

find_package(seL4 REQUIRED)
find_package(elfloader-tool REQUIRED)
sel4_configure_platform_settings()
sel4_import_kernel()
sel4_import_libsel4()

add_subdirectory("${UTIL_LIBS}/libcpio" libcpio)

# The elfloader reads the root task's path from this target's property
add_custom_target(rootserver_image)
set_property(TARGET rootserver_image PROPERTY ROOTSERVER_IMAGE "${ONCE_IMAGE}")

elfloader_import_project()
