import HeytingLean.Probability.InfoTheory.FinDist
import HeytingLean.Probability.InfoTheory.Entropy
import HeytingLean.Probability.InfoTheory.MutualInfo
import HeytingLean.Silicon

/-!
# HeytingLean: Speaking to Silicon

Standalone formalization of silicon information leakage.

This bundle contains:
- **Probability.InfoTheory**: Finite distributions, entropy, mutual information
- **Silicon**: Leakage model, signatures, early-abort, PUF formalization

## Quick Verification

```bash
cd RESEARCHER_BUNDLE
lake build --wfail
```

## Citation

Part of the HeytingLean formalization project.
See: https://github.com/Abraxas1010/HeytingLean
-/
