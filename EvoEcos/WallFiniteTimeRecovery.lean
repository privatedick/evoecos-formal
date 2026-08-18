/-
WallFiniteTimeRecovery: Finite Recovery Time Under Wall Activation
===================================================================

When L1 stability drops below 0.4 (L3WallInvariant fires), the wall blocks L3
and L1 recovers at rate r1 per step (vs r0 without wall). For p < r1/h (feasible zone),
recovery to 0.4 is GUARANTEED in finite steps:

  T = ⌈(0.4 − s₀) / (r1 − p·h)⌉

This file proves:
  1. Recovery rate r1 − p·h > 0 in the feasible zone  (linear stability)
  2. The wall activation threshold 0.4 < θ* = r0/h    (EMA detects before L1 hits floor)
  3. No net recovery in infeasible zone p ≥ r1/h       (wall cannot help)
  4. No-wall dynamics decrease L1 when p > θ*          (why wall matters)
  5. Finite recovery exists (Archimedean argument)      (core result)
  6. Witness monotonicity: same T works for higher s    (upward closure)
  7. Equivalence: profitable ↔ in feasible zone         (cost-benefit bridge)
  8. Recovery from zero (worst case, s = 0)             (NoCollapse boundary)
  9. Deployment safety: profitable + below threshold → recovery guaranteed
 10. Double-margin composition: θ* < p < p** → both profitable + finite recovery

System parameters (mirror stable_bootstrap_arch.py):
  r0 = 0.05  (_WALL_RECOVERY_OFF)   r1 = 0.10  (_WALL_RECOVERY_ON)
  h  = 0.12  (_WALL_HARM_RATE)
  θ* = r0/h = 5/12 ≈ 0.417         p** = r1/h = 5/6 ≈ 0.833

Architecture change (iter 21):
  StableBootstrapArch.wall_expected_recovery_steps(p):
    ⌈(0.4 − l1_stability) / (r1 − p·h)⌉  (0 when already above threshold or infeasible)
-/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic
import EvoEcos.WallCostBenefit

noncomputable section

namespace WallFiniteTimeRecovery

open WallCostBenefit

/-- The L1-stability threshold at which L3 is blocked (L3WallInvariant invariant). -/
abbrev wall_act_threshold : ℝ := 2 / 5

/-! ## Core Recovery Theorems -/

/-- Theorem 1: In the feasible zone (p < r1/h), the wall provides a net positive
    recovery rate: r1 − p·h > 0. Direct corollary of WallCostBenefit.wall_profitable_iff. -/
theorem recovery_rate_pos (p : ℝ) (hp : p < r1 / h) :
    r1 - p * h > 0 := (wall_profitable_iff p).mpr hp

/-- Theorem 2: The L3 wall activation threshold (0.4) is strictly below θ*
    (the ACD/EMA boundary r0/h ≈ 0.417).  This means the EMA-based threat
    detector fires before (or as) L1 stability falls to the wall floor,
    giving a detection lead of θ* − 0.4 ≈ 0.017. -/
theorem wall_threshold_below_theta_star : wall_act_threshold < r0 / h := by norm_num

/-- Theorem 3: In the infeasible zone (p ≥ r1/h), the wall cannot provide
    positive net recovery — r1 − p·h ≤ 0. -/
theorem infeasible_no_net_recovery (p : ℝ) (hp : r1 / h ≤ p) :
    r1 - p * h ≤ 0 := by
  have hval : r1 / h = 5 / 6 := by norm_num
  have hr1v : r1 = (10 : ℝ) / 100 := by norm_num
  have hhv  : h = (12 : ℝ) / 100 := by norm_num
  rw [hval] at hp
  rw [hr1v, hhv]
  nlinarith

/-- Theorem 4: Without the wall (recovery rate r0), whenever p > θ* the
    L1 stability decreases each step.  Direct corollary of
    WallCostBenefit.theta_star_earliest_needed. -/
theorem no_wall_decreasing (p : ℝ) (hp : r0 / h < p) :
    r0 - p * h < 0 := theta_star_earliest_needed p hp

/-- Theorem 5 (Core): In the feasible zone, L1 recovery is GUARANTEED in
    finite wall-active steps.  Starting from any s ∈ [0, wall_act_threshold),
    there exists T : ℕ such that  s + T · (r1 − p·h) ≥ wall_act_threshold.
    Proof: Archimedean property on the gap (threshold − s) / rate. -/
theorem finite_recovery_exists (s p : ℝ)
    (_hs0 : 0 ≤ s) (_hs : s < wall_act_threshold)
    (_hp0 : 0 ≤ p) (hp : p < r1 / h) :
    ∃ T : ℕ, s + (T : ℝ) * (r1 - p * h) ≥ wall_act_threshold := by
  have hrate : r1 - p * h > 0 := recovery_rate_pos p hp
  obtain ⟨T, hT⟩ := exists_nat_gt ((wall_act_threshold - s) / (r1 - p * h))
  refine ⟨T, ?_⟩
  have h1 : (wall_act_threshold - s) / (r1 - p * h) * (r1 - p * h) = wall_act_threshold - s :=
    div_mul_cancel₀ (wall_act_threshold - s) (ne_of_gt hrate)
  have key := mul_lt_mul_of_pos_right hT hrate
  rw [h1] at key
  linarith

/-- Theorem 6: Upward closure of witnesses — if T wall-active steps are
    sufficient to recover from s₀, they are also sufficient from any s₁ ≥ s₀. -/
theorem recovery_witness_upclosed (s0 s1 : ℝ) (p : ℝ)
    (h_ord : s0 ≤ s1)
    (T : ℕ) (hT : s0 + (T : ℝ) * (r1 - p * h) ≥ wall_act_threshold) :
    s1 + (T : ℝ) * (r1 - p * h) ≥ wall_act_threshold := by
  linarith

/-- Theorem 7: Equivalence between "profitable wall" and "feasible zone".
    Direct restatement of WallCostBenefit.wall_profitable_iff. -/
theorem wall_profitable_iff_feasible (p : ℝ) :
    r1 - p * h > 0 ↔ p < r1 / h := wall_profitable_iff p

/-- Theorem 8: Recovery from the worst case — starting from L1 = 0
    (the NoCollapse boundary), recovery is still guaranteed. -/
theorem recovery_from_zero (p : ℝ) (_hp0 : 0 ≤ p) (hp : p < r1 / h) :
    ∃ T : ℕ, (T : ℝ) * (r1 - p * h) ≥ wall_act_threshold := by
  have hrate : r1 - p * h > 0 := recovery_rate_pos p hp
  obtain ⟨T, hT⟩ := exists_nat_gt (wall_act_threshold / (r1 - p * h))
  refine ⟨T, ?_⟩
  have h1 : wall_act_threshold / (r1 - p * h) * (r1 - p * h) = wall_act_threshold :=
    div_mul_cancel₀ wall_act_threshold (ne_of_gt hrate)
  have key := mul_lt_mul_of_pos_right hT hrate
  rw [h1] at key
  linarith

/-- Theorem 9: Wall deployment safety — if the wall is profitable
    and L1 is below threshold, recovery is guaranteed. -/
theorem wall_deployment_guarantees_recovery (s p : ℝ)
    (hs0 : 0 ≤ s) (hs : s < wall_act_threshold)
    (hp0 : 0 ≤ p) (hwall : r1 - p * h > 0) :
    ∃ T : ℕ, s + (T : ℝ) * (r1 - p * h) ≥ wall_act_threshold :=
  finite_recovery_exists s p hs0 hs hp0 ((wall_profitable_iff p).mp hwall)

/-- Theorem 10 (Composition): In the double-margin zone θ* < p < p**,
    the wall is BOTH necessary (no-wall decreases L1) AND sufficient
    (finite recovery guaranteed).  Composes with WallCostBenefit.double_margin. -/
theorem double_margin_recovery (p : ℝ)
    (hp_above : r0 / h < p)
    (hp_below : p < r1 / h) :
    r0 - p * h < 0 ∧
    r1 - p * h > 0 ∧
    ∀ s : ℝ, 0 ≤ s → s < wall_act_threshold →
      ∃ T : ℕ, s + (T : ℝ) * (r1 - p * h) ≥ wall_act_threshold := by
  refine ⟨theta_star_earliest_needed p hp_above, (wall_profitable_iff p).mpr hp_below,
          fun s hs0 hs_lt => ?_⟩
  have hp0 : 0 ≤ p :=
    le_of_lt (lt_trans (by norm_num : (0 : ℝ) < r0 / h) hp_above)
  exact finite_recovery_exists s p hs0 hs_lt hp0 hp_below

end WallFiniteTimeRecovery

end
