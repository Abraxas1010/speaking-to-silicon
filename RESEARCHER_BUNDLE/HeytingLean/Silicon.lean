/-!
# Speaking to Silicon

Finite, discrete formalization layer for silicon information leakage.

Runs are modeled as joint distributions P(S × O) where S is internal state and O is observable.
Leakage is mutual information I(S; O).

## Modules

- **Model**: Core `Run` type as `FinDist (S × O)`
- **Leakage**: Mutual information definitions and independence theorem
- **Signature**: Device distinguishability via observable distributions
- **EarlyAbort**: Prefix-based prediction and accuracy
- **Empirical**: Data → FinDist bridge
- **Predictability**: Accuracy bounds and non-independence witnesses
- **Cost**: Early-abort energy savings model
- **Channel**: Stochastic channel scaffold
- **PUF**: Physical unclonable function formalization
- **Examples**: Concrete finite examples

Note: QuantumBridge (optional quantum-classical interface) is not included in this
standalone bundle. See the full HeytingLean repository for quantum integration.
-/

import HeytingLean.Silicon.Model
import HeytingLean.Silicon.Leakage
import HeytingLean.Silicon.Signature
import HeytingLean.Silicon.EarlyAbort
import HeytingLean.Silicon.Empirical
import HeytingLean.Silicon.Predictability
import HeytingLean.Silicon.Cost
import HeytingLean.Silicon.Channel
import HeytingLean.Silicon.PUF
import HeytingLean.Silicon.Examples
