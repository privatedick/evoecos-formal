# ProvablyCorrectControllers

A Lean 4 library of verified properties for minimal neural network controllers and safety architectures.

All theorems compile with **0 `sorry`** and **0 axioms**.

## Contents

### BangBangTheorem

Proves that minimal MLP policies (H=1 hidden unit, argmax over 2 actions) converge to bang-bang (sign-based) controllers, and that this structure provides maximal noise robustness.

Key results:
- **Tanh saturation**: |z| > 2 implies |tanh z| > 24/25
- **Noise robustness**: If |z(s)| > kappa and ||w||_1 * delta < kappa, then sign(z(s + epsilon)) = sign(z(s))
- **Safe zone**: States where |z| >= kappa form a region where the action is invariant under bounded noise

### ObservationalDichotomy

The Architecture-Counterfactual Dichotomy (ACD): a structural partition of measurement problems into verifiable and unverifiable classes, plus the meta-observation fixed point.

Key results:
- **ACD(i)**: Architectural setups admit perfect proactive estimators
- **ACD(ii)**: Counterfactual setups admit no perfect proactive estimator
- **Meta-observation fixed point**: Adding architectural truth values to observations does not refine the equivalence kernel
- **Non-expansion**: A system cannot expand its architectural class through recursive self-reflection

### SafetyBoundary

A three-condition characterization of when a safety interlock (binary "wall") provides benefit.

Key results:
- **Triple condition**: Wall benefit > 0 iff (low dimension AND simple dynamics AND perturbation)
- **Independence**: The three conditions are logically independent
- **Boundary theorem**: Combined positive + negative + independence statement

## Usage

This library is designed to be imported into any Lean 4 project that needs verified properties about neural network controllers or safety architectures.

```lean
import ProvablyCorrectControllers.BangBangTheorem
import ProvablyCorrectControllers.ObservationalDichotomy
import ProvablyCorrectControllers.SafetyBoundary

-- Example: using the bang-bang noise robustness theorem
open ProvablyCorrectControllers

-- Given an H1Policy p, observation s, noise epsilon:
-- If p.z s > kappa and p.lm.l1Norm * delta < kappa,
-- then the perturbed pre-activation preserves sign.
```

## Dependencies

| Component | Version |
|-----------|---------|
| Lean      | v4.3.0  |
| Mathlib   | v4.3.0  |

No external dependencies beyond Mathlib. No EvoEcos-specific types.

## Verification

```bash
cd formal/lean
lake build
```

Expected output: all files compile with 0 errors, 0 warnings.

## Project Structure

```
ProvablyCorrectControllers/
  README.md                     -- This file
  BangBangTheorem.lean          -- Minimal MLP noise robustness
  ObservationalDichotomy.lean   -- ACD: verifiable vs unverifiable
  SafetyBoundary.lean           -- Three-condition wall characterization
ProvablyCorrectControllers.lean -- Root import file
```

## Origin

These theorems were extracted and generalized from the [EvoEcos](https://github.com/user/evoecos) project's Lean 4 formal proofs. The original proofs are in `formal/lean/EvoEcos/` and remain unchanged. This library removes all EvoEcos-specific dependencies (layer types, system state, transition system) while preserving the core mathematical content.

## What is NOT here (TODO)

The following EvoEcos theorems could not be cleanly extracted due to deep dependencies on EvoEcos-specific types:

- **Layer invariants** (NoCollapse, L3WallInvariant, etc.) — depend on L1State, L2State, L3State, L4State and the full transition system
- **Inductive invariant proof** (all_reachable_states_satisfy_invariant) — depends on the full TransKind/Step/Reachable machinery
- **L4 liveness** (l4_canAlwaysActEventually, l4_boundedLearning) — depends on L4State
- **ACD alignment corollary** (alignment_impossibility_corollary) — depends on AlignmentWorld and SystemState

To extract these, one would need to define generic interfaces for "layered systems with walls" and "transition systems with invariants", which would be a significant abstraction effort.
