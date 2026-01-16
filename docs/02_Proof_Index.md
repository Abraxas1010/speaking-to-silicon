# Proof Index

## Core Theorems

### Leakage Module

| Declaration | Type | Statement |
|-------------|------|-----------|
| `Leakage` | abbrev | Leakage := mutualInfo |
| `Independent` | def | P = prodMarginals P |
| `leakage_nonneg_of_prodMarginals_Pos` | theorem | 0 ≤ Leakage P |
| `leakage_eq_zero_of_independent` | theorem | Independent P → Leakage P = 0 |

### Predictability Module

| Declaration | Type | Statement |
|-------------|------|-----------|
| `accuracy` | def | Success probability of predictor |
| `maxMass` | def | Maximum single-point probability (baseline) |
| `accuracy_prod` | theorem | Accuracy under product = accuracy under marginal |
| `accuracy_le_baseline_of_independent` | theorem | Independent → accuracy ≤ maxMass |
| `not_independent_of_accuracy_gt_baseline` | theorem | accuracy > maxMass → ¬Independent |

### Cost Module

| Declaration | Type | Statement |
|-------------|------|-----------|
| `continueProb` | def | Probability of continuing to round k |
| `expectedRounds` | def | Expected number of rounds |
| `energySavings` | def | Normalized energy savings |
| `energySavings_theoreticalMax` | theorem | Theoretical max savings = 1 - k/n |

### Signature Module

| Declaration | Type | Statement |
|-------------|------|-----------|
| `exists_pmf_ne_of_ne` | theorem | P ≠ Q → ∃ a, P.pmf a ≠ Q.pmf a |
| `exists_singleton_prob_ne` | theorem | P ≠ Q → ∃ singleton with different probability |

### PUF Module

| Declaration | Type | Statement |
|-------------|------|-----------|
| `PUF` | abbrev | Dev → Chal → FinDist Resp |
| `DistinguishableAt` | def | F d₁ c ≠ F d₂ c |
| `exists_singleton_response_prob_ne` | theorem | Distinguishability witness |

### Channel Module

| Declaration | Type | Statement |
|-------------|------|-----------|
| `Channel` | abbrev | S → FinDist O |
| `joint` | def | Prior × Channel → Joint distribution |
| `stateMarginal_joint` | theorem | State marginal of joint = prior |
| `obsMarginal_joint` | theorem | Observable marginal = mixture |

## Information Theory Foundation

### FinDist Module

| Declaration | Type | Statement |
|-------------|------|-----------|
| `FinDist` | structure | Finite probability distribution |
| `FinDist.Pos` | def | Strictly positive distribution |
| `prod` | def | Product distribution |
| `marginalLeft` | def | Left marginal |
| `marginalRight` | def | Right marginal |
| `probEvent_nonneg` | theorem | 0 ≤ P(E) |
| `probEvent_le_one` | theorem | P(E) ≤ 1 |

### Entropy Module

| Declaration | Type | Statement |
|-------------|------|-----------|
| `entropy` | def | H(X) = -Σ p log p |
| `entropy_eq_neg_sum_mul_log_of_Pos` | theorem | Alternative formula for positive distributions |

### MutualInfo Module

| Declaration | Type | Statement |
|-------------|------|-----------|
| `mutualInfo` | def | I(X;Y) via KL divergence |
| `mutualInfo_nonneg_of_Pos` | theorem | 0 ≤ I(X;Y) |

### KL Module

| Declaration | Type | Statement |
|-------------|------|-----------|
| `klDiv` | def | D(P||Q) |
| `klDiv_nonneg_of_Pos` | theorem | 0 ≤ D(P||Q) |
