/-
ProvablyCorrectControllers — A Lean 4 library of verified properties
for minimal neural network controllers and safety architectures.

This library extracts and generalises formal results originally developed
for the EvoEcos project (Stable Epistemic Bootstrap architecture) into
reusable, framework-agnostic theorems.

## Contents

* `BangBangTheorem` — Minimal MLP policies converge to finite automata;
  noise robustness of sign-based output policies.
* `ObservationalDichotomy` — The Architecture-Counterfactual Dichotomy (ACD):
  a structural partition of measurement problems into verifiable and
  unverifiable classes, plus the meta-observation fixed point.
* `SafetyBoundary` — A three-condition characterisation of when a safety
  interlock (wall mechanism) provides benefit: low intrinsic dimension,
  simple causal dynamics, and perturbation present.

## Dependencies

* Lean 4 (v4.3.0)
* Mathlib (v4.3.0)

## Verification

```bash
lake build
```

All theorems compile with 0 `sorry` and 0 axioms.
-/

import ProvablyCorrectControllers.BangBangTheorem
import ProvablyCorrectControllers.ObservationalDichotomy
import ProvablyCorrectControllers.SafetyBoundary
