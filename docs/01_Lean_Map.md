# Lean Module Map

## Structure

```
HeytingLean/
├── Probability/
│   └── InfoTheory/
│       ├── Core.lean          # safeLog, klTerm, entropyTerm
│       ├── FinDist.lean       # Finite distributions
│       ├── Entropy.lean       # Shannon entropy
│       ├── KL.lean            # KL divergence
│       ├── MutualInfo.lean    # Mutual information
│       └── Conditional.lean   # Conditional distributions
├── Silicon/
│   ├── Model.lean             # Run type definition
│   ├── Leakage.lean           # Leakage as I(S;O)
│   ├── Signature.lean         # Device distinguishability
│   ├── EarlyAbort.lean        # Prefix prediction
│   ├── Empirical.lean         # Data → FinDist
│   ├── Predictability.lean    # Accuracy bounds
│   ├── Cost.lean              # Energy savings
│   ├── Channel.lean           # Stochastic channels
│   ├── PUF.lean               # Physical unclonable functions
│   └── Examples.lean          # Concrete examples
└── Tests/
    └── Silicon/
        └── SiliconSanity.lean # Sanity checks
```

## Module Dependencies

```
Core ─────────────────────────────────────────┐
  │                                           │
  ▼                                           │
FinDist ──────────────────────────────────────┤
  │                                           │
  ├──▶ Entropy                                │
  │                                           │
  ├──▶ KL ─────────────────────────────────┐  │
  │                                        │  │
  ├──▶ MutualInfo ◀────────────────────────┘  │
  │         │                                 │
  │         ▼                                 │
  │    Conditional                            │
  │                                           │
  ▼                                           │
Silicon/Model ◀───────────────────────────────┘
  │
  ├──▶ Leakage (uses MutualInfo)
  │
  ├──▶ Signature
  │
  ├──▶ EarlyAbort
  │
  ├──▶ Empirical
  │
  ├──▶ Predictability (uses Leakage)
  │
  ├──▶ Cost
  │
  ├──▶ Channel
  │
  └──▶ PUF
```
