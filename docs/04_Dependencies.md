# Dependencies

## Direct Dependencies

| Package | Version | Purpose |
|---------|---------|---------|
| Lean 4 | 4.24.0 | Language runtime |
| Mathlib | v4.24.0 | Mathematical library |

## Mathlib Imports Used

### Analysis

- `Mathlib.Analysis.SpecialFunctions.Log.Basic` — Real logarithm for entropy

### Data Structures

- `Mathlib.Data.Fintype.BigOperators` — Summation over finite types
- `Mathlib.Data.Real.Basic` — Real numbers

## No External Runtime Dependencies

The formalization:
- Uses only Lean's standard library at runtime
- All Mathlib usage is compile-time only
- No FFI or native code dependencies

## Dependency Graph

```
speaking-to-silicon
       │
       └── mathlib4 (v4.24.0)
              │
              ├── Qq
              ├── Aesop
              ├── Batteries
              └── (transitive deps)
```

## Updating Dependencies

To update to newer Mathlib:

1. Edit `lakefile.lean`:
   ```lean
   require mathlib from git
     "https://github.com/leanprover-community/mathlib4" @ "vX.Y.Z"
   ```

2. Run:
   ```bash
   lake update
   lake build
   ```

3. Fix any API changes (rare for stable Mathlib releases)
