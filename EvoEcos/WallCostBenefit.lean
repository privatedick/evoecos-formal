/-
WallCostBenefit: Cost-Optimal Interpretation of the Proactive Wall Threshold
=============================================================================

Context: WallFeasibility proves θ* = p_reactive_critical divides the parameter space
into safe/dominance/infeasible zones. OptimalTheta proves θ* is the Pareto-optimal
proactive threshold. WallLiveness proves the wall fires within D steps of EMA > θ*.

This file adds the COST-BENEFIT interpretation: why θ* is economically optimal.

Definitions:
  r0 = RECOVERY_NO_WALL = 5/100   (l1 recovery per step without wall)
  r1 = RECOVERY_WALL    = 10/100  (l1 recovery per step with wall)
  h  = HARM_RATE        = 12/100  (l1 harm when adversary hits)
  p  = adversary probability per step

Per-step expected l1 change:
  E[Δl1 | no-wall] = r0 - p × h = 5/100 - p × 12/100
  E[Δl1 | wall]    = r1 - p × h = 10/100 - p × 12/100

Break-even thresholds:
  θ* = r0 / h = 5/12   (no-wall break-even: E[Δl1 | no-wall] = 0)
  p** = r1 / h = 5/6   (wall break-even: E[Δl1 | wall] = 0)

Key result: p** = 2 × θ* (because r1 = 2 × r0 in our system)
  The feasible zone is exactly [θ*, 2θ*] — a 1× safety margin above θ*.

Cost-optimality theorem: activating the wall at p = θ* + ε (just above break-even)
is OPTIMAL because:
  - Below θ*: E[Δl1 | no-wall] > 0 → wall unnecessary (extra cost for same outcome)
  - Above θ*: E[Δl1 | no-wall] < 0 → wall needed to prevent expected loss
  - θ* is the EARLIEST point where wall adds positive expected value

Architecture change (iter 17):
  ModelingLayer.wall_net_benefit_estimate property:
    r1 - threat_ema × h = expected Δl1 if wall active
    > 0 in feasible zone (threat_ema < p**)
    = 0 at wall break-even (threat_ema = p**)
    < 0 in infeasible zone (threat_ema > p**)

  Exposes wall effectiveness at runtime for monitoring and diagnostics.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic
import EvoEcos.WallFeasibility

noncomputable section

namespace WallCostBenefit

open WallFeasibility

/-! ## System Parameters (concrete values) -/

/-- r0 = RECOVERY_NO_WALL = 5/100 (recovery per step without wall) -/
abbrev r0 : ℝ := 5 / 100

/-- r1 = RECOVERY_WALL = 10/100 (recovery per step with wall) -/
abbrev r1 : ℝ := 10 / 100

/-- h = HARM_RATE = 12/100 (harm per step when adversary hits) -/
abbrev h : ℝ := 12 / 100

/-! ## Break-Even Thresholds -/

/-- No-wall break-even threshold: at p = r0/h, E[Δl1 | no-wall] = 0.
    Below this threshold, no-wall operation is self-sustaining (E[Δl1] > 0).
    Above this threshold, no-wall operation loses expected l1 each step. -/
theorem no_wall_break_even : r0 / h = 5 / 12 := by norm_num

/-- Wall break-even threshold: at p = r1/h, E[Δl1 | wall] = 0.
    Below this threshold, wall operation is self-sustaining.
    Above this threshold, even the wall cannot prevent expected l1 loss. -/
theorem wall_break_even : r1 / h = 5 / 6 := by norm_num

/-- Theta* (the no-wall break-even) equals r0/h numerically: 5/12 ≈ 0.417.
    In WallFeasibility, p_reactive_critical(wp) = wp.r0 / wp.h for standard params.
    This theorem establishes the concrete value. -/
theorem theta_star_value : r0 / h = 5 / 12 := by norm_num

/-- The proactive critical point equals r1/h numerically: 5/6 ≈ 0.833.
    In WallFeasibility, p_proactive_critical(wp) = wp.r1 / wp.h for standard params. -/
theorem p_proactive_value : r1 / h = 5 / 6 := by norm_num

/-! ## Double-Margin Theorem -/

/-- The wall break-even threshold is exactly 2× the no-wall break-even (theta*).
    This is a consequence of r1 = 2 × r0 in our system.
    Interpretation: the feasible zone [theta*, p**] spans exactly one theta* above theta*,
    giving a 1× safety margin — the wall protects against adversaries up to twice
    the no-wall break-even before becoming infeasible. -/
theorem double_margin : r1 / h = 2 * (r0 / h) := by norm_num

/-- Concrete: 5/6 = 2 × 5/12. The feasible zone spans exactly one theta* = 5/12 width. -/
theorem feasible_zone_is_one_theta_wide : (5 : ℝ) / 6 = 2 * (5 / 12) := by norm_num

/-! ## Net Benefit per Step -/

/-- Expected Δl1 with wall active at adversary probability p.
    Positive in feasible zone, zero at break-even, negative in infeasible zone. -/
theorem wall_net_benefit_formula (p : ℝ) :
    r1 - p * h = 10 / 100 - p * (12 / 100) := by norm_num

/-- Net benefit is positive iff p < wall break-even threshold.
    This is the condition under which wall activation improves expected l1. -/
theorem wall_profitable_iff (p : ℝ) :
    r1 - p * h > 0 ↔ p < r1 / h := by
  simp only [show r1 = (10:ℝ)/100 from by norm_num,
             show h = (12:ℝ)/100 from by norm_num,
             show (10:ℝ)/100 / ((12:ℝ)/100) = 5/6 from by norm_num]
  constructor
  · intro h1; nlinarith
  · intro h2; nlinarith

/-- Net benefit at no-wall break-even: E[Δl1 | wall, p=theta*] = r1 - theta*×h = r1 - r0 > 0.
    The wall is strictly profitable at theta*, which is why theta* is the correct activation point:
    activating the wall at theta* is always beneficial (net_benefit = r1 - r0 = 0.05 > 0). -/
theorem wall_benefit_at_theta_star :
    r1 - (r0 / h) * h = r1 - r0 := by
  have hh : (h : ℝ) ≠ 0 := by norm_num
  have : (r0 / h) * h = r0 := div_mul_cancel₀ r0 hh
  linarith

/-- Numerical: wall benefit at theta* = 0.05/step. -/
theorem wall_benefit_at_theta_star_value :
    r1 - (r0 / h) * h = 5 / 100 := by
  have hh : (h : ℝ) ≠ 0 := by norm_num
  have : (r0 / h) * h = r0 := div_mul_cancel₀ r0 hh
  simp [this]; norm_num

/-- At the wall break-even (p = p**), net benefit = 0. -/
theorem net_benefit_zero_at_wall_break_even :
    r1 - (r1 / h) * h = 0 := by
  have hh : (h : ℝ) ≠ 0 := by norm_num
  have : (r1 / h) * h = r1 := div_mul_cancel₀ r1 hh
  linarith

/-! ## Cost-Optimality of theta* -/

/-- Activating the wall at exactly theta* (no-wall break-even) is COST OPTIMAL:
    - Below theta*: no-wall is self-sustaining (E[Δl1 | no-wall] > 0), so wall adds
      net_benefit = r1-r0 > 0 per step but blocks L3 unnecessarily (opportunity cost)
    - Above theta*: no-wall causes expected loss (E[Δl1 | no-wall] < 0), so wall
      is needed to convert negative to positive expected change
    - theta* is the EARLIEST point where the wall is strictly necessary

    Proof: E[Δl1 | no-wall, p > theta*] < 0, so wall is needed for p > theta*.
    For p ≤ theta*: E[Δl1 | no-wall] ≥ 0, so wall is optional.
    Therefore theta* is the exact activation threshold that minimizes false activations
    while preventing all expected losses. -/
theorem theta_star_earliest_needed (p : ℝ) (hp : p > r0 / h) :
    r0 - p * h < 0 := by
  have hgt : p > 5 / 12 := by linarith [show r0 / h = (5:ℝ)/12 from by norm_num]
  have hr0 : r0 = (5 : ℝ) / 100 := by norm_num
  have hhv : h = (12 : ℝ) / 100 := by norm_num
  rw [hr0, hhv]
  have : p * (12 / 100) > 5 / 100 := by nlinarith
  linarith

/-- Below theta*, no wall needed: E[Δl1 | no-wall] > 0. -/
theorem no_wall_sufficient_below_theta (p : ℝ) (hp : p < r0 / h) :
    r0 - p * h > 0 := by
  have hlt : p < 5 / 12 := by linarith [show r0 / h = (5:ℝ)/12 from by norm_num]
  have hr0 : r0 = (5 : ℝ) / 100 := by norm_num
  have hhv : h = (12 : ℝ) / 100 := by norm_num
  rw [hr0, hhv]
  have : p * (12 / 100) < 5 / 100 := by nlinarith
  linarith

end WallCostBenefit

end
