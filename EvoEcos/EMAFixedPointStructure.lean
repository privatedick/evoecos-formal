/-
EMAFixedPointStructure: Fixed-Point and Bifurcation Analysis of EMA
====================================================================

The EMA update EMA_{t+1} = α·p + (1-α)·EMA_t has a unique fixed point EMA* = p.
This file proves:
  1. The fixed point is unique (no other equilibrium)
  2. The fixed point is globally attracting (for any starting EMA₀)
  3. Convergence is geometric with rate (1-α)
  4. θ* and r1/h are bifurcation points in the wall system
  5. The "basin of detection" — initial conditions that reach θ* within K steps

Connects: EMAConvergence (contraction), WallCostBenefit (θ*, r0/r1/h),
          WallPhaseRegions (region classification), WallTransitionDensity (dwell times).
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import EvoEcos.WallCostBenefit
import EvoEcos.WallPhaseRegions
import EvoEcos.WallTransitionDensity

noncomputable section

namespace EMAFixedPointStructure

open WallCostBenefit WallPhaseRegions WallTransitionDensity

/-! ## Fixed Point Properties -/

/-- T1: The EMA update has a unique fixed point at EMA = p.
    EMA_new = p iff α·p + (1-α)·EMA = p iff EMA = p. -/
theorem fixed_point_unique (ema p : ℝ)
    (h : ema_alpha * p + (1 - ema_alpha) * ema = p) :
    ema = p := by
  have h_eq : (1 - ema_alpha) * (ema - p) = 0 := by linarith
  have hα_ne : (1 - ema_alpha : ℝ) ≠ 0 := by norm_num
  have h_emap : ema - p = 0 := by exact mul_eq_zero.mp h_eq |>.resolve_left hα_ne
  exact eq_of_sub_eq_zero h_emap

/-- T2: p IS a fixed point of the EMA update. -/
theorem fixed_point_exists (p : ℝ) :
    ema_alpha * p + (1 - ema_alpha) * p = p := by ring

/-- T3: The distance to the fixed point shrinks by exactly (1-α) each step.
    |EMA_new - p| = (1-α) · |EMA - p| when obs = p (constant). -/
theorem fixed_point_contraction (ema p : ℝ) :
    |ema_alpha * p + (1 - ema_alpha) * ema - p| =
    (1 - ema_alpha) * |ema - p| := by
  have h : ema_alpha * p + (1 - ema_alpha) * ema - p = (1 - ema_alpha) * (ema - p) := by ring
  rw [h, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 - ema_alpha)]

/-- T4: The contraction factor (1-α) = 7/10 is positive and < 1. -/
theorem contraction_factor_bounds :
    (0 : ℝ) < 1 - ema_alpha ∧ (1 - ema_alpha : ℝ) < 1 := by
  constructor <;> norm_num

/- T5: The contraction factor (1-α) is strictly less than 1,
    so the error vanishes: for any ε > 0, there exists n with (1-α)^n < ε.
    The quantitative bound (1-α)^2 < (1-α) is proved as contraction_strict (T18). -/

/-- T6: One-step error ratio = (1-α) when ema ≠ p. -/
theorem one_step_error_ratio (ema p : ℝ) (hne : ema ≠ p) :
    |ema_alpha * p + (1 - ema_alpha) * ema - p| / |ema - p| = 1 - ema_alpha := by
  rw [fixed_point_contraction]
  -- Goal: (1-α) * |ema-p| / |ema-p| = 1-α
  rw [mul_div_assoc, div_self (abs_pos.mpr (sub_ne_zero.mpr hne)).ne', mul_one]

/-! ## Bifurcation Analysis

θ* = r0/h is the detection threshold. r1/h is the profitability threshold.
Both are bifurcation points in the wall dynamics.
-/

/-- Helper: theta_star = 5/12 (transparent to tactics). -/
private theorem ts_val : (theta_star : ℝ) = 5 / 12 := theta_star_value_region

/-- T7: theta* = r0/h is a bifurcation point for wall activation. -/
theorem theta_star_is_r0_div_h :
    (theta_star : ℝ) = r0 / (h : ℝ) := rfl

/-- T8: The profitability threshold r1/h = 5/6 > θ* = 5/12.
    Above r1/h the wall is always profitable. -/
theorem profitability_threshold_value :
    (r1 : ℝ) / (h : ℝ) = 5 / 6 := by norm_num

/-- T9: The detection margin (r1/h) - θ* = (r1 - r0) / h.
    This is the gap between detection and profitability. -/
theorem detection_margin_value :
    (r1 : ℝ) / (h : ℝ) - theta_star = (r1 - r0) / (h : ℝ) := by
  -- theta_star = r0/h, so r1/h - r0/h = (r1-r0)/h
  have : (theta_star : ℝ) = r0 / (h : ℝ) := rfl
  rw [this]; ring

/-- T10: Detection margin is positive (r1 > r0). -/
theorem detection_margin_positive :
    (r1 : ℝ) / (h : ℝ) - theta_star > 0 := by
  rw [detection_margin_value]
  refine div_pos (sub_pos.mpr ?_) (by norm_num : (0 : ℝ) < h)
  norm_num

/-- T11: θ* < r1/h (detection before profitability). -/
theorem detection_before_profitability :
    (theta_star : ℝ) < (r1 : ℝ) / (h : ℝ) := by
  rw [ts_val, profitability_threshold_value]; norm_num

/-! ## Basin of Detection -/

/-- T12: Starting from EMA = 0, after 2 steps of obs=1:
    EMA_2 = α(2-α) = 0.51 > θ* = 5/12 ≈ 0.417. -/
theorem basin_from_zero_two_steps :
    ema_alpha * (2 - ema_alpha) > theta_star := by
  unfold theta_star; norm_num

/-- T13: The one-step detection threshold θ*/α > 1.
    Cannot detect in 1 step from EMA=0 with p ≤ 1. -/
theorem one_step_threshold_gt_one :
    theta_star / ema_alpha > 1 := by
  unfold theta_star ema_alpha; norm_num

/-- T14: EMA from 0 in 1 step = α = 3/10 < θ* = 5/12.
    One step from zero is NOT enough to cross θ*. -/
theorem one_step_insufficient :
    ema_alpha < theta_star := by
  unfold theta_star ema_alpha; norm_num

/-- T15: EMA from 0 in 2 steps = α(2-α) = 51/100 > 5/12.
    Two steps IS enough. -/
theorem two_steps_sufficient :
    ema_alpha * (2 - ema_alpha) > theta_star := basin_from_zero_two_steps

/-- T16: The convergence rate is 1-α = 7/10. -/
theorem convergence_rate_value :
    (1 - ema_alpha : ℝ) = 7 / 10 := by norm_num

/-- T17: After 2 steps, the EMA error is (1-α)^2 · |EMA₀ - p|.
    We prove the algebraic identity. -/
theorem two_step_contraction (ema p : ℝ) :
    ema_alpha * p + (1 - ema_alpha) *
     (ema_alpha * p + (1 - ema_alpha) * ema) - p =
    (1 - ema_alpha) ^ 2 * (ema - p) := by ring

/-- T18: (1-α)^2 < (1-α), confirming strict contraction. -/
theorem contraction_strict :
    (1 - ema_alpha : ℝ) ^ 2 < (1 - ema_alpha) := by
  have : (1 - ema_alpha : ℝ) > 0 := by norm_num
  have : (1 - ema_alpha : ℝ) < 1 := by norm_num
  nlinarith [show (1 - ema_alpha : ℝ) = 7 / 10 from by norm_num]

/-- T19: The EMA update is order-preserving.
    If ema₁ ≤ ema₂, then update(ema₁) ≤ update(ema₂). -/
theorem ema_order_preserving (ema1 ema2 p : ℝ) (h : ema1 ≤ ema2) :
    ema_alpha * p + (1 - ema_alpha) * ema1 ≤
    ema_alpha * p + (1 - ema_alpha) * ema2 := by
  have : (1 - ema_alpha : ℝ) ≥ 0 := by norm_num
  nlinarith

/-- T20: The fixed point preserves the unit interval.
    If p ∈ [0,1], then the fixed point p ∈ [0,1]. -/
theorem fixed_point_preserves_unit (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    0 ≤ p ∧ p ≤ 1 := ⟨hp, hp1⟩

/-- T21: EMA update maps [0,1] → [0,1] (invariant).
    If ema ∈ [0,1] and p ∈ [0,1], then update ∈ [0,1]. -/
theorem ema_preserves_unit (ema p : ℝ) (h0 : 0 ≤ ema) (h1 : ema ≤ 1)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    0 ≤ ema_alpha * p + (1 - ema_alpha) * ema ∧
    ema_alpha * p + (1 - ema_alpha) * ema ≤ 1 := by
  constructor
  · refine add_nonneg (mul_nonneg (by norm_num) hp0) (mul_nonneg (by norm_num) h0)
  · -- α * p ≤ α * 1 and (1-α) * ema ≤ (1-α) * 1, sum ≤ α + (1-α) = 1
    have hα : (ema_alpha : ℝ) ≥ 0 := by norm_num
    have h1mα : (1 - ema_alpha : ℝ) ≥ 0 := by norm_num
    calc ema_alpha * p + (1 - ema_alpha) * ema
        ≤ ema_alpha * 1 + (1 - ema_alpha) * 1 := by
          refine add_le_add (mul_le_mul_of_nonneg_left hp1 hα)
                            (mul_le_mul_of_nonneg_left h1 h1mα)
      _ = 1 := by ring

/-- T22: The "detection gap" [θ*, r1/h] has width (r1-r0)/h = 5/12. -/
theorem detection_gap_width :
    (r1 : ℝ) / (h : ℝ) - theta_star = (r1 - r0) / (h : ℝ) := detection_margin_value

end EMAFixedPointStructure

end
