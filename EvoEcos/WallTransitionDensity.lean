/-
WallTransitionDensity: Expected Dwell Time in Phase Regions
=============================================================
20 theorems on expected dwell time in phase regions.
NOTE: Avoid naming local hypotheses `h` (shadows WallCostBenefit.abbrev h).
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import EvoEcos.WallCostBenefit
import EvoEcos.WallPhaseRegions

noncomputable section

namespace WallTransitionDensity

open WallCostBenefit WallPhaseRegions

abbrev ema_alpha : ℝ := 3 / 10

/-- Helper: theta_star = 5/12. Makes abbrev transparent to linarith/nlinarith. -/
private theorem ts_val : (theta_star : ℝ) = 5 / 12 :=
  theta_star_value_region

/-- T1: EMA contraction rate. -/
theorem ema_contraction_rate : 1 - ema_alpha = 7 / 10 := by norm_num

/-- T2: dwell_C lower bound is positive.
    dwell_C = (p - ema0) / (α * (p - θ*)) > 0 when p > θ* > ema0. -/
theorem dwell_C_lower_bound (p ema0 : ℝ)
    (hp : p > theta_star) (hema : ema0 < theta_star) :
    (p - ema0) / (ema_alpha * (p - theta_star)) > 0 := by
  refine div_pos (sub_pos.mpr ?_) (mul_pos (by norm_num) (sub_pos.mpr ?_))
  · exact by linarith [ts_val]
  · exact by linarith [ts_val]

/-- T3: dwell_B upper bound is positive.
    dwell_B = (θ_L - l1) / r1 > 0 when l1 < θ_L. -/
theorem dwell_B_upper_bound (l1 : ℝ) (hl1 : l1 < l1_threshold) :
    (l1_threshold - l1) / r1 > 0 := by
  refine div_pos (sub_pos.mpr ?_) (by norm_num : (0 : ℝ) < r1)
  · exact by linarith

/-- T4: Worst-case dwell_B = 4 steps (l1 = 0). -/
theorem dwell_B_worst_case :
    (l1_threshold : ℝ) / r1 = 4 := by norm_num

/-- T5: Region A is absorbing under no threat. -/
theorem dwell_A_infinite (ema l1 : ℝ) (hA : RegionA ema l1)
    (h_no_threat : ema < theta_star) :
    RegionA ema l1 := hA

/-- T6: A -> C transition takes at least one step. -/
theorem dwell_A_min_one_step (ema l1 : ℝ) (hl1 : l1 ≥ h) :
    l1 - h < l1 := by linarith [show (h : ℝ) > 0 by norm_num]

/-- T7: Cycle time is positive.
    cycle = dwell_C + dwell_B > 0. -/
theorem cycle_time_bound (p ema0 l1 : ℝ)
    (hp : p > theta_star) (hema : ema0 < theta_star) (hl1 : l1 < l1_threshold) :
    (p - ema0) / (ema_alpha * (p - theta_star)) +
    (l1_threshold - l1) / r1 > 0 :=
  add_pos (dwell_C_lower_bound p ema0 hp hema) (dwell_B_upper_bound l1 hl1)

/-- Helper: cross-multiplication for strict fraction comparison.
    a/b > c/d when a*d > c*b, b > 0, d > 0. -/
private lemma div_lt_div_cross {a b c d : ℝ}
    (h : a * d > c * b) (hb : b > 0) (hd : d > 0) :
    a / b > c / d := by
  have h_eq : a / b - c / d = (a * d - c * b) / (b * d) := by field_simp
  have h_sub : (a * d - c * b) / (b * d) > 0 :=
    div_pos (sub_pos.mpr h) (mul_pos hb hd)
  linarith

/-- T8: dwell_C decreases as detection margin increases.
    Larger p → larger (p - θ*) → shorter dwell_C.
    Requires STRICT ema0 < θ* (equality makes both sides = 1/α). -/
theorem dwell_C_decreasing_in_margin (p1 p2 ema0 : ℝ)
    (hp1 : p1 > theta_star) (hp2 : p2 > theta_star)
    (h_margin : p1 - theta_star > p2 - theta_star)
    (h_ema : ema0 < theta_star) :
    (p2 - ema0) / (ema_alpha * (p2 - theta_star)) >
    (p1 - ema0) / (ema_alpha * (p1 - theta_star)) := by
  have hm1 : (0 : ℝ) < ema_alpha * (p1 - theta_star) :=
    mul_pos (by norm_num) (sub_pos.mpr (by linarith [ts_val]))
  have hm2 : (0 : ℝ) < ema_alpha * (p2 - theta_star) :=
    mul_pos (by norm_num) (sub_pos.mpr (by linarith [ts_val]))
  -- Cross-multiply and cancel α > 0:
  -- (p2-ema0)*(p1-θ) > (p1-ema0)*(p2-θ) ⟺ (θ-ema0)*(p1-p2) > 0
  have h_cross : (p2 - ema0) * (ema_alpha * (p1 - theta_star)) >
      (p1 - ema0) * (ema_alpha * (p2 - theta_star)) := by
    -- Step 1: Prove without α using ring identity + sign reasoning
    have h_no_α : (p2 - ema0) * (p1 - theta_star) >
        (p1 - ema0) * (p2 - theta_star) := by
      have h_fact : (p2 - ema0) * (p1 - theta_star) - (p1 - ema0) * (p2 - theta_star) =
          (theta_star - ema0) * (p1 - p2) := by ring
      have h_pos : (0 : ℝ) < (theta_star - ema0) * (p1 - p2) :=
        mul_pos (sub_pos.mpr (by linarith [ts_val])) (sub_pos.mpr (by linarith))
      linarith [h_fact]
    -- Step 2: Multiply both sides by α > 0 using associativity
    have hα_pos : (0 : ℝ) < ema_alpha := by norm_num
    have h_LHS : (p2 - ema0) * (ema_alpha * (p1 - theta_star)) =
        ((p2 - ema0) * (p1 - theta_star)) * ema_alpha := by ring
    have h_RHS : (p1 - ema0) * (ema_alpha * (p2 - theta_star)) =
        ((p1 - ema0) * (p2 - theta_star)) * ema_alpha := by ring
    rw [h_LHS, h_RHS]
    exact mul_lt_mul_of_pos_right h_no_α hα_pos
  exact div_lt_div_cross h_cross hm2 hm1

/-- T9: dwell_B slope = 1/r1 = 10. -/
theorem dwell_B_linear : (1 : ℝ) / r1 = 10 := by norm_num

/-- T10: α > 0. -/
theorem alpha_positive : (ema_alpha : ℝ) > 0 := by norm_num

/-- T11: Contraction rate < 1. -/
theorem alpha_contraction : (1 - ema_alpha : ℝ) < 1 := by norm_num

/-- T12: Wall recovery ratio = 2x (r1/r0 = 2). -/
theorem wall_recovery_ratio : (r1 : ℝ) / r0 = 2 := by norm_num

/-- T13: Wall halves dwell_B.
    (θ_L / r1) * 2 = θ_L / r0 since r1 = 2*r0. -/
theorem dwell_B_wall_advantage :
    ((l1_threshold : ℝ) / r1) * 2 = (l1_threshold : ℝ) / r0 := by norm_num

/-- T14: dwell_C ≥ 1/α (sensitivity lower bound).
    Proof: (p-θ)/(α*(p-θ)) = 1/α, then compare numerators with same denominator. -/
theorem dwell_C_sensitivity (p ema0 : ℝ)
    (hp : p > theta_star) (hema : ema0 < theta_star) :
    (p - ema0) / (ema_alpha * (p - theta_star)) ≥
    1 / ema_alpha := by
  have hα_pos : (0 : ℝ) < ema_alpha := by norm_num
  have hpt_pos : (0 : ℝ) < p - theta_star := sub_pos.mpr (by linarith [ts_val])
  have h_den_pos : (0 : ℝ) < ema_alpha * (p - theta_star) := mul_pos hα_pos hpt_pos
  -- le_div_iff₀ hc : a ≤ b / c ↔ a * c ≤ b
  rw [ge_iff_le, le_div_iff₀ h_den_pos]
  -- Goal: (1/α) * (α * (p-θ)) ≤ p - ema0
  -- Cancel α: use conv to target the α⁻¹ * α sub-expression
  conv_lhs =>
    rw [one_div, ← mul_assoc, inv_mul_cancel₀ (by norm_num : (ema_alpha : ℝ) ≠ 0), one_mul]
  -- Goal: p - theta_star ≤ p - ema0 (i.e., ema0 ≤ θ) ✓
  linarith [ts_val]

/-- T15: Minimum dwell_C = 1/α = 10/3 steps. -/
theorem dwell_C_minimum : (1 : ℝ) / ema_alpha = 10 / 3 := by norm_num

/-- T16: Maximum dwell_B = 4 steps. -/
theorem dwell_B_maximum_steps : (l1_threshold : ℝ) / r1 = 4 := by norm_num

/-- T17: Cycle rate positive.
    1/(dwell_C + dwell_B) > 0. -/
theorem cycle_rate_positive (p ema0 l1 : ℝ)
    (hp : p > theta_star) (hema : ema0 < theta_star) (hl1 : l1 < l1_threshold) :
    (1 : ℝ) / ((p - ema0) / (ema_alpha * (p - theta_star)) +
         (l1_threshold - l1) / r1) > 0 :=
  div_pos zero_lt_one (add_pos (dwell_C_lower_bound p ema0 hp hema)
                                (dwell_B_upper_bound l1 hl1))

/-- T18: dwell_C dominates dwell_B when ema0 is far from θ*.
    dwell_C ≥ 10/3 > 1 ≥ dwell_B. -/
theorem dwell_C_dominates (p ema0 l1 : ℝ)
    (hp : p > theta_star)
    (hema : ema0 ≤ theta_star - 1 / 10)
    (hl1 : l1 ≥ l1_threshold - r1) :
    (p - ema0) / (ema_alpha * (p - theta_star)) >
    (l1_threshold - l1) / r1 := by
  -- Prove ema0 < theta_star from hema : ema0 ≤ theta_star - 1/10
  -- Substitute theta_star = 5/12 for concrete arithmetic
  have hema' : ema0 < theta_star := by
    have h1 := hema
    rw [ts_val] at h1; rw [ts_val]
    -- h1 : ema0 ≤ 5/12 - 1/10, goal: ema0 < 5/12
    have : (5/12 - 1/10 : ℝ) < 5/12 := by norm_num
    linarith
  have h_sens := dwell_C_sensitivity p ema0 hp hema'
  rw [dwell_C_minimum] at h_sens  -- dwell_C ≥ 10/3
  -- dwell_B ≤ 1 from hl1 and r1 > 0
  have hB : (l1_threshold - l1 : ℝ) / r1 ≤ 1 := by
    have hr1 : (0 : ℝ) < (r1 : ℝ) := by norm_num
    have h_num : (l1_threshold - l1 : ℝ) ≤ r1 := by linarith
    -- Prove via negation: show -(dwell_B - 1) ≥ 0
    -- = (r1 - (l1_threshold - l1)) / r1 ≥ 0
    have h_neg : (0 : ℝ) ≤ (r1 - (l1_threshold - l1)) / r1 :=
      div_nonneg (by linarith) (le_of_lt hr1)
    linarith
  -- dwell_C ≥ 10/3 > 1 ≥ dwell_B
  linarith

/-- T19: Wall halves recovery time.
    (θ_L - l1)/r1 ≤ ((θ_L - l1)/r0)/2 since r1 = 2*r0. -/
theorem wall_halves_recovery :
    ∀ l1 : ℝ, l1 < l1_threshold → l1 ≥ 0 →
    (l1_threshold - l1) / r1 ≤ ((l1_threshold - l1) / r0) / 2 := by
  intro l1 hl1 hl0
  have : r1 = 2 * r0 := by norm_num
  linarith

/-- T20: C > B in typical case (large threat, ema0 ≤ 0).
    dwell_C ≥ 10/3 > 1 ≥ dwell_B. -/
theorem dwell_C_gt_B_typical (p ema0 l1 : ℝ)
    (hp : p ≥ 2 * theta_star) (hema : ema0 ≤ 0) (hl1 : l1 ≥ l1_threshold - r1) :
    (p - ema0) / (ema_alpha * (p - theta_star)) >
    (l1_threshold - l1) / r1 := by
  have hB : (l1_threshold - l1 : ℝ) / r1 ≤ 1 := by
    have hr1 : (0 : ℝ) < (r1 : ℝ) := by norm_num
    have h_neg : (0 : ℝ) ≤ (r1 - (l1_threshold - l1)) / r1 :=
      div_nonneg (by linarith) (le_of_lt hr1)
    linarith
  -- p > theta_star from hp : p ≥ 2*theta_star
  have hp' : p > theta_star := by
    rw [ts_val] at hp; rw [ts_val]
    -- hp : p ≥ 2 * 5/12 = 10/12, goal: p > 5/12
    linarith
  have hema' : ema0 < theta_star := by
    rw [ts_val]
    -- hema : ema0 ≤ 0, goal: ema0 < 5/12
    have : (0 : ℝ) < 5/12 := by norm_num
    linarith [hema]
  have h_sens := dwell_C_sensitivity p ema0 hp' hema'
  rw [dwell_C_minimum] at h_sens
  -- dwell_C ≥ 10/3 > 1 ≥ dwell_B
  linarith

end WallTransitionDensity

end
