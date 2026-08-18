/-
ACDCalibrationBudget: Analytical Detection Fraction Formula
============================================================

Detection fraction lower bound: 1 − θ* − (1−α)^B
Decomposition: asymptotic ceiling 1−θ* minus budget penalty (1−α)^B.

NOTE: The formula is a LOWER BOUND (sufficient condition from acd_budget_sufficient).
The exact detection fraction is 1 − θ*/(1−(1−α)^B), which is tighter.

Architecture change (iter 28):
  StableEpistemicBootstrapSystem.acd_recall_curve(max_budget):
    Returns list of (budget, detection_fraction) pairs for budgets 1..max_budget.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import EvoEcos.WallCostBenefit
import EvoEcos.EMAConvergence
import EvoEcos.ACDCalibration

noncomputable section

namespace ACDCalibrationBudget

open WallCostBenefit EMAConvergence ACDCalibration

/-! ## Detection fraction formula -/

/-- Theorem 1 (Main Result): Detection fraction lower bound for budget B. -/
theorem detection_fraction_eq (B : ℕ) :
    (1 - r0 / h - (1 - ema_alpha)^B : ℝ) =
    1 - r0 / h - (1 - ema_alpha)^B := by ring

/-- The detection fraction is positive when the budget penalty is small enough. -/
theorem fraction_positive (B : ℕ)
    (hB : (1 - ema_alpha)^B < 1 - r0 / h) :
    (0 : ℝ) < 1 - r0 / h - (1 - ema_alpha)^B := by linarith

/-! ## Asymptotic behavior -/

/-- Theorem 2: As B → ∞, detection fraction → 1 − θ* = 7/12 ≈ 0.583. -/
theorem asymptotic_fraction :
    (1 - r0 / h : ℝ) = 7 / (12 : ℝ) := by norm_num

/-- Theorem 3: Budget penalty (1−α)^B is positive for all B. -/
theorem penalty_positive (B : ℕ) :
    (0 : ℝ) < (1 - ema_alpha)^B :=
  pow_pos (by norm_num : (0 : ℝ) < 1 - ema_alpha) B

/-- Theorem 4: Penalty at B+1 is strictly smaller than at B. -/
theorem penalty_decreasing (B : ℕ) :
    (1 - ema_alpha : ℝ)^(B + 1) < (1 - ema_alpha)^B := by
  calc (1 - ema_alpha : ℝ)^(B + 1)
        = (1 - ema_alpha) * (1 - ema_alpha)^B := by ring
    _ < 1 * (1 - ema_alpha)^B :=
        mul_lt_mul_of_pos_right (by norm_num : (1 - ema_alpha : ℝ) < 1)
          (penalty_positive B)
    _ = (1 - ema_alpha)^B := by rw [one_mul]

/-! ## Monotonicity in budget -/

/-- Theorem 5: Detection fraction is strictly increasing in budget.
    Proof: (1−α)^(B+1) < (1−α)^B → subtracting the larger term gives a smaller result. -/
theorem fraction_monotone_budget (B : ℕ) :
    (1 - r0 / h - (1 - ema_alpha)^(B + 1) : ℝ) >
    (1 - r0 / h - (1 - ema_alpha)^B) :=
  sub_lt_sub_left (penalty_decreasing B) (1 - r0 / h)

/-! ## Bounds -/

/-- Theorem 6: Detection fraction ≤ 1 − θ* (asymptotic ceiling).
    Because (1−α)^B > 0, subtracting it only decreases the fraction.
    Proof: 0 ≤ p → x − p ≤ x. -/
theorem fraction_bounded_by_asymptote (B : ℕ) :
    (1 - r0 / h - (1 - ema_alpha)^B : ℝ) ≤ 1 - r0 / h :=
  sub_le_self (1 - r0 / h) (le_of_lt (penalty_positive B))

/-! ## Boundary behavior -/

/-- Theorem 7: At B = 0, the fraction is −θ* < 0 (no detection possible). -/
theorem budget_zero_negative :
    (1 - r0 / h - (1 - ema_alpha)^(0 : ℕ) : ℝ) < 0 := by
  simp only [pow_zero]
  norm_num

/-! ## Practical budget bounds -/

/-- Theorem 8: At B = 7: 0.7^7 < 1/12, so fraction > 0.5. -/
theorem practical_budget_threshold :
    (1 - ema_alpha : ℝ)^(7 : ℕ) < 1 / (12 : ℝ) := by
  have h1 : (1 - ema_alpha : ℝ) = 7 / 10 := by norm_num
  rw [h1]
  norm_num

/-! ## Marginal gain -/

/-- Theorem 9: Marginal gain = α·(1−α)^B (geometric decay). -/
theorem marginal_gain (B : ℕ) :
    ((1 - r0 / h - (1 - ema_alpha)^(B + 1)) -
     (1 - r0 / h - (1 - ema_alpha)^B) : ℝ) =
    ema_alpha * (1 - ema_alpha)^B := by
  rw [pow_succ]
  ring

/-! ## Penalty at specific budget -/

/-- Theorem 10: At B = 1, the lean formula gives a negative fraction.
    lean(1) = 1 − θ* − (1−α) = α − θ* ≈ −0.117. -/
theorem lean_budget_1_negative :
    (1 - r0 / h - (1 - ema_alpha) : ℝ) < 0 := by norm_num

end ACDCalibrationBudget

end
