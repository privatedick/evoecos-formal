/-
Persuasion Power Bound
======================

**Date:** 2026-08-10

Persuasion as a *unitary framing operator* in quantum cognition: a belief state
`|ψ⟩` at angle `φ` is rotated by `θ` before a decision measurement in the basis
`e₀`, so `P(yes) = cos²(φ)` becomes `cos²(φ + θ)`. The *persuasion power* is the
decision shift `cos²(φ + θ) − cos²(φ)`.

This file proves the tight bound behind the E-experiment result R2:

    |cos²(φ + θ) − cos²(φ)| ≤ |sin θ|.

The identity `cos²(φ+θ) − cos²(φ) = −sin(2φ+θ)·sin θ` shows the bound is tight
(equality when `|sin(2φ+θ)| = 1`). The defensive reading: bounding the framing
budget `θ` bounds the achievable persuasion power by `sin` of that budget — a
persuader with a small rotation budget can move a decision by at most `sin θ`.
This is the coherent-operator complement to the Danilov & Lambert-Mogiliansky
reachability result (unconstrained *measurement* sequences reach any state).

Target: 0 sorry / 0 axiom.
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic

namespace EvoEcos.Persuasion

open Real

/-- Persuasion power of a framing rotation `θ` on a state at angle `φ`, with the
decision measured in the reference basis. -/
noncomputable def power (φ θ : ℝ) : ℝ := cos (φ + θ) ^ 2 - cos φ ^ 2

/-- Closed form: the decision shift is `−sin(2φ+θ)·sin θ`. -/
theorem power_eq (φ θ : ℝ) :
    power φ θ = -(sin (2 * φ + θ) * sin θ) := by
  unfold power
  have hsub := cos_sub_cos (2 * (φ + θ)) (2 * φ)
  have e1 : (2 * (φ + θ) + 2 * φ) / 2 = 2 * φ + θ := by ring
  have e2 : (2 * (φ + θ) - 2 * φ) / 2 = θ := by ring
  rw [e1, e2] at hsub
  rw [cos_sq (φ + θ), cos_sq φ]
  rw [show (1 / 2 + cos (2 * (φ + θ)) / 2) - (1 / 2 + cos (2 * φ) / 2)
        = (cos (2 * (φ + θ)) - cos (2 * φ)) / 2 by ring, hsub]
  ring

/-- **R2 (tight persuasion power bound).** A framing rotation `θ` can shift the
decision by at most `|sin θ|`, for every belief state `φ`. -/
theorem power_le_abs_sin (φ θ : ℝ) : |power φ θ| ≤ |sin θ| := by
  rw [power_eq, abs_neg, abs_mul]
  have h1 : |sin (2 * φ + θ)| ≤ 1 :=
    abs_le.2 ⟨neg_one_le_sin _, sin_le_one _⟩
  calc |sin (2 * φ + θ)| * |sin θ|
      ≤ 1 * |sin θ| := mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
    _ = |sin θ| := one_mul _

/-- The bound is achievable: at `φ` with `2φ+θ = π/2` the shift equals `sin θ`
in magnitude, so `power_le_abs_sin` is tight (not a loose over-estimate). -/
theorem power_tight (θ : ℝ) :
    |power ((π / 2 - θ) / 2) θ| = |sin θ| := by
  rw [power_eq, abs_neg, abs_mul]
  have : 2 * ((π / 2 - θ) / 2) + θ = π / 2 := by ring
  rw [this, sin_pi_div_two, abs_one, one_mul]

end EvoEcos.Persuasion
