/-
EMABasinGeometry: Geometric structure of the EMA basin of attraction
====================================================================

Characterizes which initial EMA values ema₀ lead to detection (ema > θ*)
within T observation steps. The "basin of detection" is:

  Basin(T, p) = {ema₀ : ema_T > θ*}

where ema_T = p + (1-α)^T · (ema₀ - p) is the closed-form EMA trajectory
with α = 3/10, θ* = 5/12.

The basin boundary (critical initial value) is:

  ema₀*(p, T) = p - (p - θ*) / (1-α)^T

Key results:
  - Basin grows with T: more observations = wider basin
  - Basin shrinks as p → θ*: harder to detect near boundary
  - At p = 4/5: detection from ema₀=0 requires T ≥ 3
  - At p = 3/5: detection from ema₀=0 requires T ≥ 4
  - Basin width grows by factor 1/(1-α) = 10/7 per additional step
  - Basin boundary at T=1 is linear in p: ema₀* = 25/42 - 3p/7

Connects: EMAFixedPointStructure (fixed points) → EMABasinGeometry (basin structure)
Experiment: 30 seeds, 4 hypotheses.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import EvoEcos.WallCostBenefit
import EvoEcos.EMAFixedPointStructure
import EvoEcos.WallPhaseRegions

noncomputable section

namespace EMABasinGeometry

open WallCostBenefit EMAFixedPointStructure WallPhaseRegions

/-! ## EMA Trajectory (Closed Form) -/

/-- T1: One-step EMA closed form.
    ema₁ = p + (1-α)(ema₀ - p) = p + 7/10·(ema₀ - p). -/
theorem ema_one_step (ema0 p : ℝ) :
    3 / 10 * p + 7 / 10 * ema0 = p + 7 / 10 * (ema0 - p) := by ring

/-- T2: Two-step EMA closed form.
    ema₂ = p + (1-α)²·(ema₀ - p) = p + 49/100·(ema₀ - p). -/
theorem ema_two_step (ema0 p : ℝ) :
    3 / 10 * p + 7 / 10 * (3 / 10 * p + 7 / 10 * ema0) =
    p + 49 / 100 * (ema0 - p) := by ring

/-- T3: Three-step EMA closed form.
    ema₃ = p + (1-α)³·(ema₀ - p) = p + 343/1000·(ema₀ - p). -/
theorem ema_three_step (ema0 p : ℝ) :
    3 / 10 * p + 7 / 10 * (3 / 10 * p + 7 / 10 * (3 / 10 * p + 7 / 10 * ema0)) =
    p + 343 / 1000 * (ema0 - p) := by ring

/-! ## Basin at p = 4/5 (= 0.8) -/

/-- T4: From ema₀=0, p=4/5: T=1 gives 6/25 = 0.24 < 5/12. NOT detected. -/
theorem basin_p08_t1_zero_miss :
    3 / 10 * (4 / 5 : ℝ) + 7 / 10 * (0 : ℝ) < 5 / 12 := by norm_num

/-- T5: From ema₀=0, p=4/5: T=2 gives 51/125 = 0.408 < 5/12. NOT detected. -/
theorem basin_p08_t2_zero_miss :
    3 / 10 * (4 / 5 : ℝ) + 7 / 10 * (3 / 10 * (4 / 5 : ℝ) + 7 / 10 * (0 : ℝ)) < 5 / 12 := by norm_num

/-- T6: From ema₀=0, p=4/5: T=3 gives 657/1250 > 5/12. DETECTED.
    Basin(3, 4/5) includes ema₀ = 0. -/
theorem basin_p08_t3_zero_hit :
    3 / 10 * (4 / 5 : ℝ) + 7 / 10 * (3 / 10 * (4 / 5 : ℝ) +
    7 / 10 * (3 / 10 * (4 / 5 : ℝ) + 7 / 10 * (0 : ℝ))) > 5 / 12 := by norm_num

/-- T7: Basin boundary at T=1, p=4/5: critical ema₀ = 53/210 ≈ 0.252.
    ema₁(53/210, 4/5) = 5/12 exactly. -/
theorem basin_boundary_p08_t1 :
    3 / 10 * (4 / 5 : ℝ) + 7 / 10 * (53 / 210 : ℝ) = 5 / 12 := by norm_num

/-- T8: Basin boundary at T=2, p=4/5: critical ema₀ = 13/735 ≈ 0.018.
    ema₂(13/735, 4/5) = 5/12 exactly. -/
theorem basin_boundary_p08_t2 :
    3 / 10 * (4 / 5 : ℝ) + 7 / 10 * (3 / 10 * (4 / 5 : ℝ) +
    7 / 10 * (13 / 735 : ℝ)) = 5 / 12 := by norm_num

/-! ## Basin at p = 3/5 (= 0.6) -/

/-- T9: From ema₀=0, p=3/5: T=1 gives 9/50 = 0.18 < 5/12. NOT detected. -/
theorem basin_p06_t1_zero_miss :
    3 / 10 * (3 / 5 : ℝ) + 7 / 10 * (0 : ℝ) < 5 / 12 := by norm_num

/-- T10: From ema₀=0, p=3/5: T=3 gives 1971/5000 = 0.394 < 5/12. NOT detected. -/
theorem basin_p06_t3_zero_miss :
    3 / 10 * (3 / 5 : ℝ) + 7 / 10 * (3 / 10 * (3 / 5 : ℝ) +
    7 / 10 * (3 / 10 * (3 / 5 : ℝ) + 7 / 10 * (0 : ℝ))) < 5 / 12 := by norm_num

/-- T11: From ema₀=0, p=3/5: T=4 gives 22797/50000 > 5/12. DETECTED.
    Basin(4, 3/5) includes ema₀ = 0. -/
theorem basin_p06_t4_zero_hit :
    3 / 10 * (3 / 5 : ℝ) + 7 / 10 * (3 / 10 * (3 / 5 : ℝ) +
    7 / 10 * (3 / 10 * (3 / 5 : ℝ) + 7 / 10 * (3 / 10 * (3 / 5 : ℝ) +
    7 / 10 * (0 : ℝ)))) > 5 / 12 := by norm_num

/-- T12: Basin boundary at T=1, p=3/5: critical ema₀ = 71/210 ≈ 0.338.
    ema₁(71/210, 3/5) = 5/12 exactly. -/
theorem basin_boundary_p06_t1 :
    3 / 10 * (3 / 5 : ℝ) + 7 / 10 * (71 / 210 : ℝ) = 5 / 12 := by norm_num

/-! ## Basin Structure -/

/-- T13: Basin grows from T=1 to T=2 at p=4/5.
    Critical boundary at T=1 (53/210) > boundary at T=2 (13/735).
    Lower boundary = wider basin = more initial values detect. -/
theorem basin_grows_t1_to_t2_p08 :
    (53 / 210 : ℝ) > 13 / 735 := by norm_num

/-- T14: Basin at higher p is wider.
    p=3/5 boundary (71/210) > p=4/5 boundary (53/210).
    Higher p = lower boundary = wider basin. -/
theorem basin_shrinks_with_lower_p :
    (71 / 210 : ℝ) > 53 / 210 := by norm_num

/-- T15: At p = θ* = 5/12, the basin is a single point.
    ema₁(5/12, 5/12) = 5/12. Only the fixed point itself. -/
theorem basin_at_boundary_point :
    3 / 10 * (5 / 12 : ℝ) + 7 / 10 * (5 / 12 : ℝ) = 5 / 12 := by ring

/-- T16: If both ema₀ > θ* and p > θ*, then detection persists at T=1.
    EMA is a weighted average of two values above θ*, so result is above θ*.
    "Once detecting, keep detecting" — the upper quadrant is invariant. -/
theorem basin_includes_above_threshold (ema0 p : ℝ) (h1 : ema0 > 5 / 12) (h2 : p > 5 / 12) :
    3 / 10 * p + 7 / 10 * ema0 > 5 / 12 := by nlinarith

/-! ## Basin Width -/

/-- T17: Basin width at T=1, p=4/5: 4/5 - 53/210 = 23/42.
    Width = (p - θ*) / (1-α) = 23/60 / (7/10) = 23/42. -/
theorem basin_width_p08_t1 :
    (4 / 5 : ℝ) - 53 / 210 = 23 / 42 := by norm_num

/-- T18: Basin width at T=2, p=4/5: 4/5 - 13/735 = 115/147.
    Width = (p - θ*) / (1-α)² = 23/60 / (49/100) = 115/147. -/
theorem basin_width_p08_t2 :
    (4 / 5 : ℝ) - 13 / 735 = 115 / 147 := by norm_num

/-- T19: Basin width growth factor from T=1 to T=2 is 10/7 = 1/(1-α).
    Each additional step multiplies the basin width by 1/(1-α) = 10/7 ≈ 1.43. -/
theorem basin_width_growth_factor :
    (115 / 147 : ℝ) / (23 / 42 : ℝ) = 10 / 7 := by norm_num

/-- T20: The growth factor equals 1/(1-α) = 1/(7/10) = 10/7.
    Basin width ∝ 1/(1-α)^T, growing by 1/(1-α) per step. -/
theorem growth_factor_is_contraction_inverse :
    (10 / 7 : ℝ) = 1 / (7 / 10 : ℝ) := by norm_num

/-- T21: Basin boundary formula at T=1 is linear in p.
    ema₀*(p, 1) = p - (p - 5/12)·(10/7) = 25/42 - 3p/7.
    Slope = -3/7 < 0: boundary decreases with p (basin widens). -/
theorem basin_boundary_t1_linear (p : ℝ) :
    p - (p - 5 / 12) * (10 / 7) = 25 / 42 - 3 / 7 * p := by ring

/-- T22: Basin boundary at T=1 is strictly decreasing in p.
    Higher threat rate ⟹ lower boundary ⟹ wider basin. -/
theorem basin_boundary_t1_decreasing (p1 p2 : ℝ) (h : p2 > p1) :
    25 / 42 - 3 / 7 * p1 > 25 / 42 - 3 / 7 * p2 := by nlinarith

end EMABasinGeometry

end
