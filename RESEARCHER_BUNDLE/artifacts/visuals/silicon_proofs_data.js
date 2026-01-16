// Speaking to Silicon - UMAP Proof Graph Data
// Auto-generated declaration map for visualization

const siliconProofsData = {
  items: [
    // InfoTheory/Core
    { name: "safeLog", kind: "def", family: "InfoTheory/Core", pos: { x: 0.15, y: 0.85, z: 0.2 } },
    { name: "klTerm", kind: "def", family: "InfoTheory/Core", pos: { x: 0.18, y: 0.82, z: 0.22 } },
    { name: "entropyTerm", kind: "def", family: "InfoTheory/Core", pos: { x: 0.12, y: 0.88, z: 0.18 } },

    // InfoTheory/FinDist
    { name: "FinDist", kind: "structure", family: "InfoTheory/FinDist", pos: { x: 0.25, y: 0.75, z: 0.3 } },
    { name: "FinDist.Pos", kind: "def", family: "InfoTheory/FinDist", pos: { x: 0.28, y: 0.72, z: 0.32 } },
    { name: "FinDist.expect_add", kind: "theorem", family: "InfoTheory/FinDist", pos: { x: 0.22, y: 0.78, z: 0.28 } },
    { name: "FinDist.probEvent_eq_sum", kind: "theorem", family: "InfoTheory/FinDist", pos: { x: 0.30, y: 0.70, z: 0.35 } },
    { name: "FinDist.prod", kind: "def", family: "InfoTheory/FinDist", pos: { x: 0.32, y: 0.68, z: 0.38 } },
    { name: "FinDist.marginalLeft", kind: "def", family: "InfoTheory/FinDist", pos: { x: 0.35, y: 0.65, z: 0.40 } },
    { name: "FinDist.marginalRight", kind: "def", family: "InfoTheory/FinDist", pos: { x: 0.38, y: 0.62, z: 0.42 } },

    // InfoTheory/Entropy
    { name: "entropy", kind: "def", family: "InfoTheory/Entropy", pos: { x: 0.20, y: 0.60, z: 0.45 } },
    { name: "entropy_eq_neg_sum_mul_log_of_Pos", kind: "theorem", family: "InfoTheory/Entropy", pos: { x: 0.23, y: 0.57, z: 0.48 } },

    // InfoTheory/KL
    { name: "klDiv", kind: "def", family: "InfoTheory/KL", pos: { x: 0.15, y: 0.55, z: 0.50 } },
    { name: "klDiv_nonneg_of_Pos", kind: "theorem", family: "InfoTheory/KL", pos: { x: 0.18, y: 0.52, z: 0.52 } },

    // InfoTheory/MutualInfo
    { name: "mutualInfo", kind: "def", family: "InfoTheory/MutualInfo", pos: { x: 0.40, y: 0.50, z: 0.55 } },
    { name: "mutualInfo_nonneg_of_Pos", kind: "theorem", family: "InfoTheory/MutualInfo", pos: { x: 0.43, y: 0.48, z: 0.58 } },

    // InfoTheory/Conditional
    { name: "condDistOfPos", kind: "def", family: "InfoTheory/Conditional", pos: { x: 0.45, y: 0.45, z: 0.60 } },
    { name: "mutualInfo_eq_sum_mul_log_ratio_of_Pos", kind: "theorem", family: "InfoTheory/Conditional", pos: { x: 0.48, y: 0.42, z: 0.62 } },

    // Silicon/Model
    { name: "Run", kind: "abbrev", family: "Silicon/Model", pos: { x: 0.55, y: 0.55, z: 0.40 } },
    { name: "Run.stateMarginal", kind: "abbrev", family: "Silicon/Model", pos: { x: 0.58, y: 0.52, z: 0.42 } },
    { name: "Run.obsMarginal", kind: "abbrev", family: "Silicon/Model", pos: { x: 0.52, y: 0.58, z: 0.38 } },

    // Silicon/Leakage
    { name: "Leakage", kind: "abbrev", family: "Silicon/Leakage", pos: { x: 0.60, y: 0.45, z: 0.50 } },
    { name: "prodMarginals", kind: "def", family: "Silicon/Leakage", pos: { x: 0.63, y: 0.42, z: 0.52 } },
    { name: "Independent", kind: "def", family: "Silicon/Leakage", pos: { x: 0.57, y: 0.48, z: 0.48 } },
    { name: "leakage_nonneg_of_prodMarginals_Pos", kind: "theorem", family: "Silicon/Leakage", pos: { x: 0.65, y: 0.40, z: 0.55 } },
    { name: "leakage_eq_zero_of_independent", kind: "theorem", family: "Silicon/Leakage", pos: { x: 0.68, y: 0.38, z: 0.58 } },

    // Silicon/Signature
    { name: "exists_pmf_ne_of_ne", kind: "theorem", family: "Silicon/Signature", pos: { x: 0.70, y: 0.60, z: 0.35 } },
    { name: "exists_singleton_prob_ne", kind: "theorem", family: "Silicon/Signature", pos: { x: 0.73, y: 0.57, z: 0.38 } },

    // Silicon/EarlyAbort
    { name: "Trace", kind: "abbrev", family: "Silicon/EarlyAbort", pos: { x: 0.75, y: 0.70, z: 0.25 } },
    { name: "takePrefix", kind: "def", family: "Silicon/EarlyAbort", pos: { x: 0.78, y: 0.67, z: 0.28 } },
    { name: "accuracy_nonneg", kind: "theorem", family: "Silicon/EarlyAbort", pos: { x: 0.72, y: 0.73, z: 0.22 } },
    { name: "accuracy_le_one", kind: "theorem", family: "Silicon/EarlyAbort", pos: { x: 0.80, y: 0.65, z: 0.30 } },

    // Silicon/Empirical
    { name: "uniform", kind: "def", family: "Silicon/Empirical", pos: { x: 0.50, y: 0.75, z: 0.20 } },

    // Silicon/Predictability
    { name: "accuracy_prod", kind: "theorem", family: "Silicon/Predictability", pos: { x: 0.82, y: 0.45, z: 0.45 } },
    { name: "maxMass", kind: "def", family: "Silicon/Predictability", pos: { x: 0.85, y: 0.42, z: 0.48 } },
    { name: "accuracy_le_baseline_of_independent", kind: "theorem", family: "Silicon/Predictability", pos: { x: 0.88, y: 0.40, z: 0.50 } },
    { name: "not_independent_of_accuracy_gt_baseline", kind: "theorem", family: "Silicon/Predictability", pos: { x: 0.90, y: 0.38, z: 0.52 } },

    // Silicon/Cost
    { name: "expectedRounds_eq_of_continueProb_eq_zero", kind: "theorem", family: "Silicon/Cost", pos: { x: 0.85, y: 0.25, z: 0.65 } },
    { name: "energySavings_eq_of_continueProb_eq_zero", kind: "theorem", family: "Silicon/Cost", pos: { x: 0.88, y: 0.22, z: 0.68 } },
    { name: "energySavings_theoreticalMax", kind: "theorem", family: "Silicon/Cost", pos: { x: 0.82, y: 0.28, z: 0.62 } },

    // Silicon/Channel
    { name: "Channel", kind: "abbrev", family: "Silicon/Channel", pos: { x: 0.65, y: 0.30, z: 0.70 } },
    { name: "stateMarginal_joint", kind: "theorem", family: "Silicon/Channel", pos: { x: 0.68, y: 0.27, z: 0.72 } },
    { name: "obsMarginal_joint", kind: "theorem", family: "Silicon/Channel", pos: { x: 0.62, y: 0.33, z: 0.68 } },

    // Silicon/PUF
    { name: "PUF", kind: "abbrev", family: "Silicon/PUF", pos: { x: 0.75, y: 0.20, z: 0.78 } },
    { name: "DistinguishableAt", kind: "def", family: "Silicon/PUF", pos: { x: 0.78, y: 0.18, z: 0.80 } },
    { name: "exists_singleton_response_prob_ne", kind: "theorem", family: "Silicon/PUF", pos: { x: 0.72, y: 0.22, z: 0.76 } },

    // Silicon/Examples
    { name: "unifBool", kind: "def", family: "Silicon/Examples", pos: { x: 0.55, y: 0.85, z: 0.15 } },
    { name: "deltaTrue", kind: "def", family: "Silicon/Examples", pos: { x: 0.58, y: 0.82, z: 0.18 } }
  ],

  // Dependency edges (index pairs)
  edges: [
    // Core -> FinDist
    [0, 3], [1, 3], [2, 3],
    // FinDist -> Entropy, KL, MutualInfo
    [3, 10], [4, 10], [3, 12], [4, 13], [3, 14], [4, 15],
    // FinDist -> Conditional
    [3, 16], [8, 16], [9, 16],
    // MutualInfo -> Leakage
    [14, 21], [15, 24],
    // Model uses FinDist
    [3, 18], [8, 19], [9, 20],
    // Leakage uses Model
    [18, 21], [19, 22], [20, 22],
    // Signature uses FinDist
    [3, 27], [3, 28],
    // EarlyAbort uses FinDist
    [3, 29], [3, 32],
    // Empirical uses FinDist
    [3, 33],
    // Predictability uses FinDist, Leakage
    [3, 34], [23, 36], [24, 37],
    // Cost standalone
    [38, 39], [38, 40],
    // Channel uses FinDist
    [3, 41], [8, 42], [9, 43],
    // PUF uses FinDist
    [3, 44], [3, 46],
    // Examples use FinDist
    [3, 47], [3, 48]
  ]
};

// Color scheme for module families
const siliconColors = {
  'InfoTheory/Core': '#a3a3a3',
  'InfoTheory/FinDist': '#5e9cff',
  'InfoTheory/Entropy': '#c77dff',
  'InfoTheory/KL': '#f472b6',
  'InfoTheory/MutualInfo': '#4ade80',
  'InfoTheory/Conditional': '#22d3d3',
  'Silicon/Model': '#fbbf24',
  'Silicon/Leakage': '#ef4444',
  'Silicon/Signature': '#fb923c',
  'Silicon/EarlyAbort': '#a78bfa',
  'Silicon/Empirical': '#6366f1',
  'Silicon/Predictability': '#14b8a6',
  'Silicon/Cost': '#eab308',
  'Silicon/Channel': '#d946ef',
  'Silicon/PUF': '#10b981',
  'Silicon/Examples': '#64748b'
};

// Export for use in viewers
if (typeof module !== 'undefined' && module.exports) {
  module.exports = { siliconProofsData, siliconColors };
}
