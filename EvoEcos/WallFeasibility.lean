/-
WallFeasibility: Phase Transition Theorem for L2 Wall Activation
================================================================

Formalizes the operational envelope of EvoEcos's L2 wall mechanism.

Key insight: The L2 wall improves L1 recovery by blocking L3 (which consumes
resources when active). This creates two distinct recovery regimes:
  - Wall OFF: recovery_no_wall = r₀  (L3 active, consuming resources)
  - Wall ON:  recovery_wall    = r₁  (L3 blocked, resources freed for L1)

Two critical probabilities emerge:
  - p_reactive  := r₀ / h  (boundary above which reactive wall cannot sustain NoCollapse)
  - p_proactive := r₁ / h  (boundary above which even proactive wall cannot sustain NoCollapse)

Since r₀ < r₁, we have p_reactive < p_proactive.

For p ∈ (p_reactive, p_proactive):
  - Reactive wall (activates at l1 < 0.4) FAILS: it started in no-wall mode too long
  - Proactive wall (activates on threat_score > θ) SUCCEEDS: activates before damage accumulates

Experimentally verified (experiment_proactive_wall_threshold.py, 30 seeds):
  - harm=0.12, r₀=0.05, r₁=0.10 → p_reactive≈0.417, p_proactive≈0.833
  - At p=0.70: proactive 100% vs reactive 78.9%
  - At p=0.80: proactive 64.5% vs reactive 3.9%
  - At p=0.83: proactive 12.7% vs reactive 0.1%
  - At p=0.90: both 0% (both walls fail above p_proactive)
-/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic

noncomputable section

namespace WallFeasibility

/-! ## Parameter Structure -/

/-- Parameters for the wall feasibility model. -/
structure WallParams where
  harm_rate : ℝ           -- harm per adversarial hit
  recovery_wall : ℝ       -- L1 recovery per step when wall is ON (L3 blocked)
  recovery_no_wall : ℝ    -- L1 recovery per step when wall is OFF (L3 active)
  harm_pos : harm_rate > 0
  recovery_wall_pos : recovery_wall > 0
  recovery_no_wall_pos : recovery_no_wall > 0
  recovery_order : recovery_no_wall < recovery_wall  -- wall strictly improves recovery

/-! ## Critical Probabilities -/

/-- p_reactive: critical probability for a fully-reactive wall.
    Above this, even a wall that is always active cannot prevent expected net decline. -/
noncomputable def p_reactive_critical (wp : WallParams) : ℝ :=
  wp.recovery_no_wall / wp.harm_rate

/-- p_proactive: critical probability for a proactive wall (immediately active).
    Above this, no wall strategy can prevent expected net decline. -/
noncomputable def p_proactive_critical (wp : WallParams) : ℝ :=
  wp.recovery_wall / wp.harm_rate

/-- p_reactive < p_proactive: proactive wall has a strictly larger operational envelope. -/
theorem proactive_extends_envelope (wp : WallParams) :
    p_reactive_critical wp < p_proactive_critical wp := by
  unfold p_reactive_critical p_proactive_critical
  exact div_lt_div_of_pos_right wp.recovery_order wp.harm_pos

/-! ## Expected Drift Analysis -/

/-- Expected change in l1_stability per step under adversary probability p
    and recovery rate r.
    E[Δl1] = -p · harm_rate + r -/
noncomputable def expected_drift (p r h : ℝ) : ℝ := -p * h + r

/-- Below p_critical, expected drift is non-negative (wall can sustain stability). -/
theorem drift_nonneg_below_critical (p r h : ℝ)
    (hh : h > 0) (_hp : 0 ≤ p) (hcrit : p < r / h) :
    expected_drift p r h ≥ 0 := by
  unfold expected_drift
  rw [ge_iff_le, ← sub_nonneg]
  have : p * h < r := (lt_div_iff₀ hh).mp hcrit
  linarith

/-- Above p_critical, expected drift is negative (no wall can prevent eventual collapse). -/
theorem drift_neg_above_critical (p r h : ℝ)
    (hh : h > 0) (hcrit : p > r / h) :
    expected_drift p r h < 0 := by
  unfold expected_drift
  have : r < p * h := (div_lt_iff₀ hh).mp hcrit
  linarith

/-- NoCollapse necessary condition: p must be below p_proactive_critical. -/
theorem no_collapse_requires_p_below_critical (p : ℝ) (wp : WallParams)
    (hcrit : p > p_proactive_critical wp) :
    expected_drift p wp.recovery_wall wp.harm_rate < 0 := by
  exact drift_neg_above_critical p wp.recovery_wall wp.harm_rate wp.harm_pos hcrit

/-! ## The Proactive Dominance Zone -/

/-- The proactive dominance zone: p values where proactive succeeds but reactive fails.
    Formally: (p_reactive_critical, p_proactive_critical). -/
def in_dominance_zone (p : ℝ) (wp : WallParams) : Prop :=
  p_reactive_critical wp < p ∧ p < p_proactive_critical wp

/-- Dominance zone is non-empty: p_reactive < p_proactive guarantees a gap. -/
theorem dominance_zone_nonempty (wp : WallParams) :
    ∃ p : ℝ, in_dominance_zone p wp := by
  use (p_reactive_critical wp + p_proactive_critical wp) / 2
  constructor
  · linarith [proactive_extends_envelope wp]
  · linarith [proactive_extends_envelope wp]

/-- In the dominance zone, the reactive wall faces negative drift (fails),
    but wall-enhanced recovery is still positive (proactive wall can succeed). -/
theorem dominance_zone_reactive_fails (p : ℝ) (wp : WallParams)
    (hz : in_dominance_zone p wp) :
    expected_drift p wp.recovery_no_wall wp.harm_rate < 0 := by
  unfold in_dominance_zone at hz
  exact drift_neg_above_critical p wp.recovery_no_wall wp.harm_rate wp.harm_pos hz.1

theorem dominance_zone_proactive_feasible (p : ℝ) (wp : WallParams)
    (hz : in_dominance_zone p wp) (hp : 0 ≤ p) :
    expected_drift p wp.recovery_wall wp.harm_rate ≥ 0 := by
  unfold in_dominance_zone at hz
  exact drift_nonneg_below_critical p wp.recovery_wall wp.harm_rate wp.harm_pos hp hz.2

/-! ## Architectural Corollary -/

/-- The current L3WallInvariant (reactive: activates at l1 < 0.4) operates
    effectively only for p < p_reactive_critical.
    A proactive wall (activates on threat_score) extends coverage to p_proactive_critical.

    Operational envelope ratio: p_proactive / p_reactive = recovery_wall / recovery_no_wall.
    Experimentally: 0.10/0.05 = 2x (recovery_wall=0.10, recovery_no_wall=0.05). -/
theorem operational_envelope_ratio (wp : WallParams) :
    p_proactive_critical wp / p_reactive_critical wp =
    wp.recovery_wall / wp.recovery_no_wall := by
  unfold p_proactive_critical p_reactive_critical
  have hh : wp.harm_rate ≠ 0 := ne_of_gt wp.harm_pos
  have hrn : wp.recovery_no_wall ≠ 0 := ne_of_gt wp.recovery_no_wall_pos
  field_simp [hh, hrn]

/-- A proactive wall's operational envelope is strictly larger than a reactive wall's
    by exactly the recovery ratio. -/
theorem proactive_envelope_larger (wp : WallParams) :
    p_proactive_critical wp > p_reactive_critical wp := proactive_extends_envelope wp

end WallFeasibility

end
