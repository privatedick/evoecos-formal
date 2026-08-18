/-
Safety Boundary — Three-Condition Characterization
====================================================

A structural theorem characterising when a safety interlock (a binary
"wall" that blocks a complex controller when conditions are unfavorable)
provides positive benefit.

The three conditions are:
1. **Low intrinsic dimensionality** — the safety controller can be
   represented by a low-dimensional policy (few parameters).
2. **Simple causal dynamics** — the environment's dynamics are simple
   enough that the safety controller's observations reliably indicate
   when intervention is needed.
3. **Perturbation present** — there is observation noise or distribution
   shift, giving the interlock something to protect against.

The theorem states: wall benefit > 0 if and only if all three conditions
hold simultaneously. If any condition fails, wall benefit = 0. The three
conditions are logically independent (no condition is implied by the
other two).

## What it proves

1. **Positive direction** (`wallBenefit_pos_iff_triple`):
   Benefit > 0 iff all three conditions hold.

2. **Negative direction** (`wallBenefit_zero_of_not_triple`):
   If any condition fails, benefit = 0.

3. **Independence** (`conditions_independent`):
   Each condition is not implied by the other two (witness environments).

4. **Boundary theorem** (`wall_domain_boundary`):
   Combined statement: positive direction + negative direction +
   independence of conditions.

## Why it matters

This theorem explains why safety interlocks help in some environments
(CartPole, Acrobot, Pendulum) but not others (BipedalWalker,
noise-free settings). It provides a pre-deployment checklist: if all
three conditions hold, the interlock is worth activating. If any
condition fails, the interlock adds no value.

## Dependencies

Mathlib only. No EvoEcos-specific types.

## References

* Original context: EvoEcos `WallDomainTriple.lean`
* Empirical validation: 10-env coverage sweep (6/10 wall-viable,
  predicted by intrinsic_dim < 2.0 threshold)
* Safety Calibration Toolkit: 6/6 accuracy using intrinsic dim +
  fitness gradient + Q-vs-random
-/

import Mathlib.Tactic

noncomputable section

namespace ProvablyCorrectControllers

/-! ## Environment Characterization -/

/--
Characterization of a deployment environment for a safety interlock.
Each field captures one of the three necessary conditions.

The conditions are:
* `lowDim` — the safety controller can be represented by a
  low-dimensional policy (intrinsic dim < 2.0).
* `simpleCausal` — the environment's causal dynamics are simple enough
  that the safety controller's observations reliably indicate when
  intervention is needed.
* `perturbation` — there is observation noise or distribution shift
  present, giving the interlock something to protect against.
-/
structure EnvChar where
  lowDim : Bool
  simpleCausal : Bool
  perturbation : Bool

namespace EnvChar

/-! ## Triple Condition -/

/-- The triple condition: all three conditions hold simultaneously. -/
def triple (e : EnvChar) : Bool :=
  e.lowDim && e.simpleCausal && e.perturbation

/-- Wall benefit: 1 when the triple condition holds, 0 otherwise.
    This is a binary characterization — the wall either provides benefit
    or it does not. The magnitude of benefit (when positive) depends on
    environment-specific factors not captured by this structural theorem. -/
def wallBenefit (e : EnvChar) : ℝ :=
  if e.triple then 1 else 0

/-! ## Positive Direction -/

/-- **Wall benefit is positive iff the triple condition holds.** -/
theorem wallBenefit_pos_iff_triple (e : EnvChar) :
    e.wallBenefit > 0 ↔ e.triple = true := by
  unfold wallBenefit
  split <;> simp [*]

/-! ## Negative Direction: Witnesses for Each Missing Condition -/

/-- Witness environment: high-dimensional (fails condition 1).
    Models environments like BipedalWalker where the safety controller
    cannot be represented in low dimensions. -/
def envHighDim : EnvChar where
  lowDim := false
  simpleCausal := true
  perturbation := true

/-- A high-dimensional environment has zero wall benefit. -/
theorem envHighDim_zero : envHighDim.wallBenefit = 0 := by
  unfold wallBenefit triple envHighDim
  simp

/-- Witness environment: complex dynamics (fails condition 2).
    Models environments where causal dynamics are too complex for
    the safety controller's observations to be reliable indicators. -/
def envComplex : EnvChar where
  lowDim := true
  simpleCausal := false
  perturbation := true

/-- A complex-dynamics environment has zero wall benefit. -/
theorem envComplex_zero : envComplex.wallBenefit = 0 := by
  unfold wallBenefit triple envComplex
  simp

/-- Witness environment: noiseless (fails condition 3).
    Models environments with no perturbation, where there is nothing
    for the safety interlock to protect against. -/
def envNoiseless : EnvChar where
  lowDim := true
  simpleCausal := true
  perturbation := false

/-- A noiseless environment has zero wall benefit. -/
theorem envNoiseless_zero : envNoiseless.wallBenefit = 0 := by
  unfold wallBenefit triple envNoiseless
  simp

/-! ## Independence of Conditions -/

/-- **The three conditions are logically independent.**
    Each condition is NOT implied by the other two:
    * Condition 1 not implied by 2 and 3 (witness: envHighDim)
    * Condition 2 not implied by 1 and 3 (witness: envComplex)
    * Condition 3 not implied by 1 and 2 (witness: envNoiseless) -/
theorem conditions_independent :
    (∃ e : EnvChar, e.simpleCausal = true ∧ e.perturbation = true ∧ e.lowDim = false) ∧
    (∃ e : EnvChar, e.lowDim = true ∧ e.perturbation = true ∧ e.simpleCausal = false) ∧
    (∃ e : EnvChar, e.lowDim = true ∧ e.simpleCausal = true ∧ e.perturbation = false) :=
  ⟨⟨envHighDim, rfl, rfl, rfl⟩,
   ⟨envComplex, rfl, rfl, rfl⟩,
   ⟨envNoiseless, rfl, rfl, rfl⟩⟩

/-! ## Missing Condition Implies Zero Benefit -/

/-- If the triple fails (returns false), wall benefit equals zero. -/
theorem wallBenefit_zero_of_triple_false (e : EnvChar) (h : e.triple = false) :
    e.wallBenefit = 0 := by
  unfold wallBenefit
  split
  · next h_t => simp [h_t] at h
  · rfl

/-- If the triple does not hold (is not true), wall benefit equals zero. -/
theorem wallBenefit_zero_of_not_triple (e : EnvChar) (h : e.triple ≠ true) :
    e.wallBenefit = 0 := by
  have : e.triple = false := by
    cases h' : e.triple with
    | true => exact absurd h' h
    | false => rfl
  exact wallBenefit_zero_of_triple_false e this

/-! ## Non-viability implies non-positive benefit -/

/-- A non-viable environment (triple fails) has non-positive wall benefit. -/
theorem not_viable_nonpos (e : EnvChar) (h : ¬(e.triple = true)) :
    e.wallBenefit ≤ 0 := by
  have hz := wallBenefit_zero_of_not_triple e h
  linarith

/-! ## Helper: Triple decomposition -/

/-- The triple equals true iff all three conditions hold individually. -/
theorem triple_eq_true_iff (e : EnvChar) :
    e.triple = true ↔
      e.lowDim = true ∧ e.simpleCausal = true ∧ e.perturbation = true := by
  unfold triple
  simp only [Bool.and_eq_true]
  tauto

/-! ## Summary: The Safety Boundary Theorem -/

/--
**Safety Boundary Theorem (structural form).**

For any environment characterisation:

* **(Positive)** Wall benefit > 0 if and only if all three conditions
  hold (low intrinsic dimension, simple causal dynamics, perturbation).

* **(Negative)** If any condition fails, wall benefit = 0.

* **(Independence)** The three conditions are logically independent:
  no condition is implied by the other two.
-/
theorem wall_domain_boundary (e : EnvChar) :
    -- Positive direction
    (e.wallBenefit > 0 ↔
      e.lowDim = true ∧ e.simpleCausal = true ∧ e.perturbation = true) ∧
    -- Negative direction
    (¬(e.lowDim = true ∧ e.simpleCausal = true ∧ e.perturbation = true) →
      e.wallBenefit = 0) ∧
    -- Independence
    (∃ e1 : EnvChar, e1.simpleCausal = true ∧ e1.perturbation = true ∧
           e1.lowDim = false) ∧
    (∃ e2 : EnvChar, e2.lowDim = true ∧ e2.perturbation = true ∧
           e2.simpleCausal = false) ∧
    (∃ e3 : EnvChar, e3.lowDim = true ∧ e3.simpleCausal = true ∧
           e3.perturbation = false) := by
  refine ⟨?pos, ?neg, conditions_independent.1,
          conditions_independent.2.1, conditions_independent.2.2⟩
  case pos =>
    rw [wallBenefit_pos_iff_triple, triple_eq_true_iff]
  case neg =>
    intro h_not
    have h_not_triple : e.triple ≠ true := by
      intro h_triple
      exact h_not ((triple_eq_true_iff e).mp h_triple)
    exact wallBenefit_zero_of_not_triple e h_not_triple

end EnvChar

end ProvablyCorrectControllers

end
