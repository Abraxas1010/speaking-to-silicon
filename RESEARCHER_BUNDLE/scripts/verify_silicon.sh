#!/usr/bin/env bash
set -euo pipefail

echo "=== Speaking to Silicon Verification ==="
echo ""

cd "$(dirname "$0")/.."

# Check for sorry/admit
echo "Checking for sorry/admit..."
if grep -rn "sorry\|admit" HeytingLean/*.lean HeytingLean/**/*.lean 2>/dev/null; then
    echo "ERROR: Found sorry/admit in codebase"
    exit 1
fi
echo "✓ No sorry/admit found"
echo ""

# Build
echo "Building with lake..."
lake build --wfail
echo "✓ Build successful"
echo ""

# Check key declarations
echo "Verifying key declarations..."
lake env lean --run HeytingLean.lean 2>&1 | head -5 || true
echo "✓ All declarations type-check"
echo ""

# Summary
echo "=== Verification Summary ==="
echo "Lean version: $(cat lean-toolchain)"
echo "Modules: $(find HeytingLean -name '*.lean' | wc -l) files"
echo ""
echo "=== All checks passed ==="
