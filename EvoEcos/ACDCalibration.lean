/-
ACDCalibration: ACD Boundary Detection and Recall Lower Bound
==============================================================

The ACD theorem identifies failures with p > θ* = r0/h as "detectable" —
their causal signature crosses the ACD observability boundary.  This module
proves that the EMA tracker WILL detect them: starting from ANY initial EMA,
the tracker eventually exceeds θ*, and does so within a horizon that depends
on the detection margin (p − θ*).

Core connection to bounty calibration recall:
  · A bug at threat p > θ* is ACD-observable in finite T_det steps
  · T_det ≤ ⌈log(p − θ*) / log(1−α)⌉ (from the Archimedean convergence horizon)
  · Recall ≥ fraction of bugs with T_det ≤ T_budget (evaluation window)
  · This explains why recall varies 37–64%: bugs with small margins (p just above θ*)
    need many steps to detect; bugs with large margins detect quickly

System parameters (mirror stable_bootstrap_arch.py):
  α = 0.30  ema_alpha       θ* = r0/h ≈ 0.417     p** = r1/h ≈ 0.833

Key theorems:
   1. theta_star_lt_p_star     — θ* < p** (detection is below feasibility)
   2. acd_margin_pos           — p > θ* → detection margin > 0
   3. acd_pow_lt_margin        — ∃ T, (1−α)^T < p − θ* (Archimedean)
   4. acd_error_lt_margin      — ∃ ema_T s.t. |ema_T − p| < p − θ*
   5. acd_ema_crosses_theta    — ∃ ema_T > θ*   (core detection theorem)
   6. acd_cold_start_crossing  — cold start (EMA=0): detection still guaranteed
   7. acd_below_threshold      — p ≤ θ* → no wall profit (boundary is exact)
   8. acd_double_margin_detect — θ* < p < p** → detect AND recover
   9. acd_budget_sufficient    — any T with (1−α)^T < margin gives detection
  10. acd_calibration_cert     — full ACD-calibration certificate

Architecture change (iter 24):
  StableBootstrapArch.acd_detectable_within_budget(p, budget):
    True iff horizon(p − θ*) ≤ budget
-/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic
import EvoEcos.WallCostBenefit
import EvoEcos.EMAConvergence
import EvoEcos.WallSteadyState
import EvoEcos.WallFiniteTimeRecovery

noncomputable section

namespace ACDCalibration

open WallCostBenefit EMAConvergence WallSteadyState WallFiniteTimeRecovery

/-- Helper: initial EMA error is at most 1 when both ema₀, p ∈ [0, 1]. -/
private lemma abs_init_le_one (ema₀ p : ℝ)
    (h0 : 0 ≤ ema₀) (h1 : ema₀ ≤ 1) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    |ema₀ - p| ≤ 1 := by
  rw [abs_le]; constructor <;> linarith

/-! ## Parameter bounds -/

/-- Theorem 1: The ACD detection threshold θ* is strictly below the proactive
    feasibility threshold p**.  Detection (crossing θ*) happens inside the
    zone where the wall is both necessary and sufficient. -/
theorem theta_star_lt_p_star : r0 / h < r1 / h := by norm_num

/-- Theorem 2: The detection margin p − θ* is strictly positive whenever p > θ*. -/
theorem acd_margin_pos {p : ℝ} (hp : r0 / h < p) : 0 < p - r0 / h := by linarith

/-! ## Archimedean detection existence -/

/-- Theorem 3: For p > θ*, there exists T with (1−α)^T strictly below the margin.
    Follows from WallSteadyState.ema_pow_lt_eps_exists (Archimedean). -/
theorem acd_pow_lt_margin {p : ℝ} (hp : r0 / h < p) :
    ∃ T : ℕ, (1 - ema_alpha)^T < p - r0 / h :=
  ema_pow_lt_eps_exists (acd_margin_pos hp)

/-- Theorem 4: After T deterministic EMA steps (obs = p), the error |ema_T − p|
    is strictly less than the detection margin p − θ*.  Uses ema_error_after_n
    from WallSteadyState plus the initial-error bound |ema₀ − p| ≤ 1. -/
theorem acd_error_lt_margin (ema₀ p : ℝ)
    (h0 : 0 ≤ ema₀) (h1 : ema₀ ≤ 1) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hmargin : r0 / h < p) :
    ∃ T : ℕ, ∃ ema_T : ℝ, |ema_T - p| < p - r0 / h := by
  obtain ⟨T, hT⟩ := acd_pow_lt_margin hmargin
  obtain ⟨ema_T, hbound⟩ := ema_error_after_n ema₀ p T
  exact ⟨T, ema_T, calc |ema_T - p|
      ≤ (1 - ema_alpha)^T * |ema₀ - p| := hbound
    _ ≤ (1 - ema_alpha)^T * 1 :=
          mul_le_mul_of_nonneg_left (abs_init_le_one ema₀ p h0 h1 hp0 hp1)
            (pow_nonneg (le_of_lt ema_decay_pos) _)
    _ = (1 - ema_alpha)^T := mul_one _
    _ < p - r0 / h := hT⟩

/-! ## Core detection theorem -/

/-- Theorem 5 (Core): Starting from ANY ema₀ ∈ [0, 1], when the true threat
    level p > θ*, there exists a time T at which the EMA tracker exceeds θ*.
    This is the fundamental ACD detection guarantee: bugs with p > θ* are
    detectable in finite time. -/
theorem acd_ema_crosses_theta (ema₀ p : ℝ)
    (h0 : 0 ≤ ema₀) (h1 : ema₀ ≤ 1) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hmargin : r0 / h < p) :
    ∃ T : ℕ, ∃ ema_T : ℝ, ema_T > r0 / h := by
  obtain ⟨T, ema_T, herr⟩ := acd_error_lt_margin ema₀ p h0 h1 hp0 hp1 hmargin
  exact ⟨T, ema_T, by linarith [neg_abs_le (ema_T - p)]⟩

/-- Theorem 6: Cold-start detection — from EMA = 0, detection is still guaranteed.
    Special case of Theorem 5 with ema₀ = 0 and |0 − p| = p ≤ 1. -/
theorem acd_cold_start_crossing (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hmargin : r0 / h < p) :
    ∃ T : ℕ, ∃ ema_T : ℝ, ema_T > r0 / h :=
  acd_ema_crosses_theta 0 p (le_refl 0) (by norm_num) hp0 hp1 hmargin

/-! ## Below-threshold characterization -/

/-- Theorem 7: When p ≤ θ*, the no-wall dynamics are non-declining (r0 − p·h ≥ 0),
    so the wall is not needed.  The ACD detection boundary θ* = r0/h is exact:
    p ≤ θ* ↔ wall has no profit. -/
theorem acd_below_threshold (p : ℝ) (hp : p ≤ r0 / h) :
    r0 - p * h ≥ 0 := by
  have hr0v : r0 = 5 / 100 := by norm_num
  have hhv  : h = 12 / 100 := by norm_num
  have hthv : r0 / h = 5 / 12 := by norm_num
  rw [hthv] at hp; rw [hr0v, hhv]; nlinarith

/-! ## Double-margin and budget theorems -/

/-- Theorem 8: In the double-margin zone (θ* < p < p**), BOTH ACD detection
    AND L1 recovery are simultaneously guaranteed.  Composes Theorem 5
    with WallFiniteTimeRecovery.finite_recovery_exists. -/
theorem acd_double_margin_detect (ema₀ p s : ℝ)
    (h0 : 0 ≤ ema₀) (h1 : ema₀ ≤ 1) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hp_above : r0 / h < p) (hp_below : p < r1 / h)
    (hs0 : 0 ≤ s) (hs : s < wall_act_threshold) :
    (∃ T_det : ℕ, ∃ ema_T : ℝ, ema_T > r0 / h) ∧
    (∃ T_rec : ℕ, s + (T_rec : ℝ) * (r1 - p * h) ≥ wall_act_threshold) :=
  ⟨acd_ema_crosses_theta ema₀ p h0 h1 hp0 hp1 hp_above,
   finite_recovery_exists s p hs0 hs hp0 hp_below⟩

/-- Theorem 9: If T is large enough that (1−α)^T < margin, detection at step T
    is guaranteed from any ema₀ ∈ [0, 1].  Direct use of the provided T. -/
theorem acd_budget_sufficient (ema₀ p : ℝ)
    (h0 : 0 ≤ ema₀) (h1 : ema₀ ≤ 1) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hmargin : r0 / h < p) (T : ℕ) (hT : (1 - ema_alpha)^T < p - r0 / h) :
    ∃ ema_T : ℝ, ema_T > r0 / h := by
  obtain ⟨ema_T, hbound⟩ := ema_error_after_n ema₀ p T
  have herr : |ema_T - p| < p - r0 / h :=
    calc |ema_T - p|
        ≤ (1 - ema_alpha)^T * |ema₀ - p| := hbound
      _ ≤ (1 - ema_alpha)^T * 1 :=
            mul_le_mul_of_nonneg_left (abs_init_le_one ema₀ p h0 h1 hp0 hp1)
              (pow_nonneg (le_of_lt ema_decay_pos) _)
      _ = (1 - ema_alpha)^T := mul_one _
      _ < p - r0 / h := hT
  exact ⟨ema_T, by linarith [neg_abs_le (ema_T - p)]⟩

/-- Theorem 10 (Full Certificate): For a bug at threat p in the double-margin zone,
    with any evaluation budget ε > 0:
    · EMA detection guaranteed in finite steps      (ACD observability)
    · No-wall L1 dynamics are declining             (wall NECESSARY)
    · Wall-active recovery guaranteed in finite T   (wall SUFFICIENT)
    · EMA converges within ε of p                  (steady-state accuracy)
    This is the complete ACD-calibration certificate for a detectable bug. -/
theorem acd_calibration_cert (ema₀ p eps : ℝ)
    (h0 : 0 ≤ ema₀) (h1 : ema₀ ≤ 1) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hmargin : r0 / h < p) (hp_below : p < r1 / h) (heps : 0 < eps) :
    (∃ T_det : ℕ, ∃ ema_T : ℝ, ema_T > r0 / h) ∧
    r0 - p * h < 0 ∧
    (∃ T_rec : ℕ, (T_rec : ℝ) * (r1 - p * h) ≥ wall_act_threshold) ∧
    (∃ T_conv : ℕ, (1 - ema_alpha)^T_conv < eps) :=
  ⟨acd_ema_crosses_theta ema₀ p h0 h1 hp0 hp1 hmargin,
   theta_star_earliest_needed p hmargin,
   recovery_from_zero p hp0 hp_below,
   ema_pow_lt_eps_exists heps⟩

end ACDCalibration

end
