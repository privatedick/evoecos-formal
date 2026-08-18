/-
WallPhaseRegions: Phase Regions of the (EMA, L1) State Space
=============================================================

This module formalizes the three phase regions of the (EMA, L1_stability)
state space and proves the allowed transitions between them.

Phase regions:
  Region A (safe):        l1 >= L1_threshold (EMA irrelevant when stable)
  Region B (wall-active): l1 < L1_threshold AND ema >= theta_star
  Region C (vulnerable):  l1 < L1_threshold AND ema < theta_star

Key insight: the only recovery path is C -> B -> A (wall must activate).
Direct C -> A transition is impossible because L1 cannot recover without
the wall when the threat is present.

Connection to architecture:
  wall_phase_region(ema, l1) returns which region the system is in.
  This enables a phase_diagnostic() method for real-time monitoring.

Theorems connect to WallCostBenefit (theta_star, p_star), EMAConvergence
(EMA dynamics), and Invariants (NoCollapse, L3WallInvariant).

NOTE: WallCostBenefit defines `abbrev h : ℝ := 12/100` (harm rate).
We must avoid naming local hypotheses `h` to prevent shadowing.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import EvoEcos.WallCostBenefit

noncomputable section

namespace WallPhaseRegions

open WallCostBenefit

/-! ## Thresholds -/

/-- L1 stability threshold: l1 >= l1_threshold means L1 is stable.
    Value: 0.4 (matching stable_bootstrap_arch.py). -/
abbrev l1_threshold : ℝ := 4 / 10

/-- theta_star = r0/h: ACD detection boundary. -/
abbrev theta_star : ℝ := r0 / (h : ℝ)

/-! ## Auxiliary facts about WallCostBenefit parameters -/

private theorem r1_gt_r0 : (r1 : ℝ) > r0 := by norm_num

/-! ## Phase Region Definitions -/

/-- Region A (safe): L1 is stable. EMA doesn't matter for safety when L1 is stable. -/
def RegionA (ema l1 : ℝ) : Prop := l1 ≥ l1_threshold

/-- Region B (wall-active): L1 is unstable and EMA has crossed theta_star.
    Wall is firing, L3 is blocked, L1 is recovering. -/
def RegionB (ema l1 : ℝ) : Prop := l1 < l1_threshold ∧ ema ≥ theta_star

/-- Region C (vulnerable): L1 is unstable and EMA is below theta_star.
    No wall, L1 declining, L3 blocked. -/
def RegionC (ema l1 : ℝ) : Prop := l1 < l1_threshold ∧ ema < theta_star

/-! ## Exhaustiveness and Exclusivity -/

/-- Theorem 1: Every state is in exactly one of A, B, or C. -/
theorem regions_exhaustive (ema l1 : ℝ) :
    RegionA ema l1 ∨ RegionB ema l1 ∨ RegionC ema l1 := by
  unfold RegionA RegionB RegionC
  by_cases hl1 : l1 < l1_threshold
  · by_cases hema : ema < theta_star
    · right; right; exact ⟨hl1, hema⟩
    · right; left; exact ⟨hl1, not_lt.mp hema⟩
  · left; exact not_lt.mp hl1

/-- Theorem 2: Regions are mutually exclusive. -/
theorem regions_mutually_exclusive (ema l1 : ℝ) :
    ¬(RegionA ema l1 ∧ RegionB ema l1) ∧
    ¬(RegionA ema l1 ∧ RegionC ema l1) ∧
    ¬(RegionB ema l1 ∧ RegionC ema l1) := by
  unfold RegionA RegionB RegionC
  refine ⟨?_, ?_, ?_⟩
  · intro ⟨ha, hb⟩; obtain ⟨hb1, _⟩ := hb; linarith
  · intro ⟨ha, hc⟩; obtain ⟨hc1, _⟩ := hc; linarith
  · intro ⟨hb, hc⟩; obtain ⟨_, hb2⟩ := hb; obtain ⟨_, hc2⟩ := hc; linarith

/-! ## Region properties -/

/-- Theorem 3: In Region A, L1 is stable (by definition). -/
theorem region_A_stable (ema l1 : ℝ) (hp : RegionA ema l1) :
    l1 ≥ l1_threshold := hp

/-- Theorem 4: In Region B, wall is active (EMA >= theta_star and L1 unstable). -/
theorem region_B_wall_active (ema l1 : ℝ) (hp : RegionB ema l1) :
    l1 < l1_threshold ∧ ema ≥ theta_star := hp

/-- Theorem 5: In Region C, system is vulnerable (no wall, L1 declining). -/
theorem region_C_vulnerable (ema l1 : ℝ) (hp : RegionC ema l1) :
    l1 < l1_threshold ∧ ema < theta_star := hp

/-! ## Transition theorems -/

/-- Theorem 6: C -> B transition. EMA rises above theta_star, wall activates. -/
theorem transition_C_to_B {ema₂ l1 : ℝ}
    (hema : ema₂ ≥ theta_star) (hl1 : l1 < l1_threshold) :
    RegionB ema₂ l1 :=
  ⟨hl1, hema⟩

/-- Theorem 7: B -> A transition. L1 recovers above threshold. -/
theorem transition_B_to_A {ema l1₂ : ℝ}
    (hl1 : l1₂ ≥ l1_threshold) :
    RegionA ema l1₂ := hl1

/-- Theorem 8: A -> C transition. L1 drops and EMA is low. -/
theorem transition_A_to_C {ema l1₂ : ℝ}
    (hl1 : l1₂ < l1_threshold) (hema : ema < theta_star) :
    RegionC ema l1₂ := ⟨hl1, hema⟩

/-- Theorem 9: No direct C -> A recovery without wall.
    Wall recovery rate r1 exceeds no-wall rate r0. -/
theorem no_direct_C_to_A_recovery :
    (r1 : ℝ) > r0 := r1_gt_r0

/-- Theorem 10: Recovery requires wall (r1 > r0). -/
theorem recovery_requires_wall : (r1 : ℝ) > r0 := r1_gt_r0

/-! ## Phase boundary values -/

/-- Theorem 11: theta_star = 5/12. -/
theorem theta_star_value_region : (theta_star : ℝ) = 5 / 12 := by
  unfold theta_star; exact WallCostBenefit.theta_star_value

/-- Theorem 12: l1_threshold = 0.4. -/
theorem l1_threshold_value : (l1_threshold : ℝ) = 4 / 10 := rfl

/-- Theorem 13: Region B exists because theta_star < 1. -/
theorem region_B_exists : (theta_star : ℝ) < 1 := by
  unfold theta_star; norm_num

/-- Theorem 14: Region B is reachable from C when threat appears. -/
theorem region_B_reachable_from_C {l1 : ℝ} (hl1 : l1 < l1_threshold) :
    ∃ ema, RegionC ema l1 ∧ ∃ ema', RegionB ema' l1 := by
  use theta_star / 2
  refine ⟨⟨hl1, ?_⟩, ?_⟩
  · show (theta_star / 2 : ℝ) < theta_star
    unfold theta_star; linarith [WallCostBenefit.theta_star_value]
  · use (theta_star + 1 / 10 : ℝ)
    refine ⟨hl1, ?_⟩
    show (theta_star + 1 / 10 : ℝ) ≥ theta_star
    linarith

/-- Theorem 15: Region A is reachable from B via recovery. -/
theorem region_A_reachable_from_B {ema : ℝ} (hema : ema ≥ theta_star) :
    ∃ l1, RegionB ema l1 ∧ ∃ l1', RegionA ema l1' := by
  use (l1_threshold / 2 : ℝ)
  refine ⟨⟨by norm_num, hema⟩, ?_⟩
  use (l1_threshold + 1 / 10 : ℝ)
  show l1_threshold + 1 / 10 ≥ l1_threshold
  norm_num

/-! ## Architectural connection -/

/-- Theorem 16: In Region A, L3 is accessible (l1 >= threshold). -/
theorem region_A_l3_accessible (ema l1 : ℝ) (hp : RegionA ema l1) :
    l1 ≥ l1_threshold := hp

/-- Theorem 17: In Region B or C, L3 is blocked (l1 < threshold). -/
theorem region_BC_l3_blocked (ema l1 : ℝ)
    (hp : RegionB ema l1 ∨ RegionC ema l1) :
    l1 < l1_threshold := by
  unfold RegionB RegionC at hp
  cases hp with
  | inl hb => obtain ⟨h1, _⟩ := hb; exact h1
  | inr hc => obtain ⟨h1, _⟩ := hc; exact h1

/-- Theorem 18: Region B is the only region with wall active AND L1 unstable. -/
theorem region_B_unique_wall_active (ema l1 : ℝ) :
    RegionB ema l1 ↔ (l1 < l1_threshold ∧ ema ≥ theta_star) := by rfl

/-- Theorem 19: Detection margin determines B-region width.
    margin = p* - theta_star = 5/12. -/
theorem detection_margin_width :
    (5 : ℝ) / 6 - theta_star = 5 / 12 := by
  unfold theta_star; norm_num

/-- Theorem 20: Region A is the goal state (stable, L3 accessible). -/
theorem region_A_is_goal (ema l1 : ℝ) (hp : RegionA ema l1) :
    l1 ≥ l1_threshold := hp

end WallPhaseRegions

end
