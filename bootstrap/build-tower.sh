#!/bin/bash
# Build the normalizer module tower from bottom to top
# Stops on first error

set -e

cd "$(dirname "$0")"

AGDA="agda --no-main"

echo "=== Building Foundations ==="

echo "[1/20] Foundations/Types"
time $AGDA normalizer/Foundations/Types.agda

echo "[2/20] Foundations/MinimalCCC"
time $AGDA normalizer/Foundations/MinimalCCC.agda

echo "[3/20] Foundations/Encoding"
time $AGDA normalizer/Foundations/Encoding.agda

echo "[4/20] Foundations/Confluence"
time $AGDA normalizer/Foundations/Confluence.agda

echo "=== Building Level0V2 Base ==="

echo "[5/20] Level0V2/Normalizer"
time $AGDA normalizer/Level0V2/Normalizer.agda

echo "[6/20] Level0V2/NoRedex"
time $AGDA normalizer/Level0V2/NoRedex.agda

echo "=== Building Level0V2/Normalize Submodules ==="

# Base modules (depend only on Foundations/NoRedex/Normalizer)
echo "[7/20] Level0V2/Normalize/Rebuild"
time $AGDA normalizer/Level0V2/Normalize/Rebuild.agda

echo "[8/20] Level0V2/Normalize/Chain"
time $AGDA normalizer/Level0V2/Normalize/Chain.agda

# Dispatch depends on Rebuild
echo "[9/20] Level0V2/Normalize/Dispatch"
time $AGDA normalizer/Level0V2/Normalize/Dispatch.agda

# NoRedexRebuild depends on Rebuild
echo "[10/20] Level0V2/Normalize/NoRedexRebuild"
time $AGDA normalizer/Level0V2/Normalize/NoRedexRebuild.agda

# Handlers depends on Chain, Dispatch
echo "[11/20] Level0V2/Normalize/Handlers"
time $AGDA normalizer/Level0V2/Normalize/Handlers.agda

# NoRedexHandlers depends on Handlers, NoRedexRebuild
echo "[12/20] Level0V2/Normalize/NoRedexHandlers"
time $AGDA normalizer/Level0V2/Normalize/NoRedexHandlers.agda

# NstepDispatch depends on NoRedexHandlers
echo "[13/20] Level0V2/Normalize/NstepDispatch"
time $AGDA normalizer/Level0V2/Normalize/NstepDispatch.agda

# Fixpoint depends on NstepDispatch
echo "[14/20] Level0V2/Normalize/Fixpoint"
time $AGDA normalizer/Level0V2/Normalize/Fixpoint.agda

# Facade depends on Fixpoint
echo "[15/20] Level0V2/Normalize (facade)"
time $AGDA normalizer/Level0V2/Normalize.agda

echo "[16/20] Level0V2/NormalizeLemmas"
time $AGDA normalizer/Level0V2/NormalizeLemmas.agda

echo "=== Building MainTheorem Submodules ==="

echo "[17/19] MainTheorem/Correctness"
time $AGDA normalizer/Level0V2/MainTheorem/Correctness.agda

echo "[18/19] MainTheorem/FixpointTheorem"
time $AGDA normalizer/Level0V2/MainTheorem/FixpointTheorem.agda

echo "[19/19] MainTheorem (facade)"
time $AGDA normalizer/Level0V2/MainTheorem.agda

echo "=== BUILD COMPLETE ==="
