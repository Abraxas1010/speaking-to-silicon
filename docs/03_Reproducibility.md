# Reproducibility

## Requirements

- **Lean**: 4.24.0 (specified in `lean-toolchain`)
- **Mathlib**: v4.24.0 (specified in `lakefile.lean`)

## Build Instructions

### Quick Build

```bash
cd RESEARCHER_BUNDLE
lake build --wfail
```

### Full Verification

```bash
cd RESEARCHER_BUNDLE
./scripts/verify_silicon.sh
```

### Expected Output

```
=== Speaking to Silicon Verification ===

Checking for sorry/admit...
✓ No sorry/admit found

Building with lake...
✓ Build successful

Verifying key declarations...
✓ All declarations type-check

=== Verification Summary ===
Lean version: leanprover/lean4:v4.24.0
Modules: 16 files

=== All checks passed ===
```

## Troubleshooting

### Lake Can't Find Mathlib

```bash
lake update
lake build
```

### Toolchain Mismatch

Ensure your Lean installation matches the toolchain:

```bash
elan override set leanprover/lean4:v4.24.0
```

### Build Fails with Type Errors

This formalization is pinned to specific Mathlib and Lean versions. API changes in newer versions may cause failures. Use the exact versions specified.
