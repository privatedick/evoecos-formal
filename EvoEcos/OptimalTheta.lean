/-
OptimalTheta: Optimal Proactive Wall Threshold
===============================================

The proactive wall fires when threat_ema > θ. In steady state (threat_ema → p),
the wall fires when p > θ, yielding expected drift:
  - Wall ON  (p > θ): E[Δl1] = -p·h + r₁  (recovery_wall)
  - Wall OFF (p ≤ θ): E[Δl1] = -p·h + r₀  (recovery_no_wall)

Two competing criteria determine the optimal threshold θ*:
  1. NoCollapse coverage: wall must fire for all p where no-wall drift < 0.
     This requires θ ≤ p_reactive_critical = r₀/h.
  2. L3 availability: minimize false activations (wall ON when unnecessary).
     This prefers θ as large as possible.

The Pareto-optimal point is θ* = p_reactive_critical = r₀/h.

Key theorems:
  - `wall_improves_drift`: wall activation always improves expected drift.
  - `theta_le_reactive_covers_zone`: θ ≤ p_reactive_critical covers entire dominance zone.
  - `theta_above_reactive_creates_gap`: any θ > p_reactive_critical leaves a coverage gap.
  - `optimal_theta_is_p_reactive_critical`: p_reactive_critical is the maximum θ that
    covers the full dominance zone (Pareto-optimal).
  - `dominance_zone_width`: Width = (r₁ - r₀) / h (safety margin from blocking L3).

Experimentally verified (experiment_optimal_theta.py, 30 seeds, 9 p-values):
  - At p=0.800: theta=0.30 (80.6%) > theta=0.417 (78.2%) > theta=0.50 (64.5%) > theta=0.60 (6.8%)
  - H3 CONFIRMED: monotone ordering theta_star ≥ theta_mid ≥ theta_hi in dominance zone
  - H2 CONFIRMED: equivalent survival below p_reactive_critical (max_diff=0.000)
-/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic
import EvoEcos.WallFeasibility

noncomputable section

namespace OptimalTheta

open WallFeasibility

/-! ## Steady-State Proactive Wall Model -/

/-- Expected drift when wall ON (p > θ): uses recovery_wall. -/
noncomputable def drift_wall_on (p : ℝ) (wp : WallParams) : ℝ :=
  expected_drift p wp.recovery_wall wp.harm_rate

/-- Expected drift when wall OFF (p ≤ θ): uses recovery_no_wall. -/
noncomputable def drift_wall_off (p : ℝ) (wp : WallParams) : ℝ :=
  expected_drift p wp.recovery_no_wall wp.harm_rate

/-- Wall activation strictly improves expected drift for any positive threat level. -/
theorem wall_improves_drift (p : ℝ) (wp : WallParams) :
    drift_wall_on p wp > drift_wall_off p wp := by
  unfold drift_wall_on drift_wall_off expected_drift
  linarith [wp.recovery_order]

/-- Wall advantage magnitude = r₁ - r₀ (independent of adversary probability p). -/
theorem wall_advantage_magnitude (p : ℝ) (wp : WallParams) :
    drift_wall_on p wp - drift_wall_off p wp = wp.recovery_wall - wp.recovery_no_wall := by
  unfold drift_wall_on drift_wall_off expected_drift
  ring

/-! ## Coverage Condition for the Dominance Zone -/

/-- When θ ≤ p_reactive_critical, every p in the dominance zone is > θ,
    so the proactive wall fires for all dangerous p values. -/
theorem theta_le_reactive_covers_zone (θ : ℝ) (wp : WallParams)
    (hθ : θ ≤ p_reactive_critical wp) (p : ℝ) (hp : in_dominance_zone p wp) :
    p > θ :=
  lt_of_le_of_lt hθ hp.1

/-- If θ > p_reactive_critical and θ < p_proactive_critical, there exist p values in the
    dominance zone where the wall does not fire (p ≤ θ) but no-wall drift is negative. -/
theorem theta_above_reactive_creates_gap (θ : ℝ) (wp : WallParams)
    (hθ : θ > p_reactive_critical wp)
    (_hθ_hi : θ < p_proactive_critical wp) :
    ∃ p : ℝ, p_reactive_critical wp < p ∧ p ≤ θ ∧ drift_wall_off p wp < 0 := by
  refine ⟨(p_reactive_critical wp + θ) / 2, by linarith, by linarith, ?_⟩
  unfold drift_wall_off
  apply drift_neg_above_critical _ _ _ wp.harm_pos
  -- Goal: (p_reactive_critical wp + θ) / 2 > wp.recovery_no_wall / wp.harm_rate
  -- p_reactive_critical wp is definitionally wp.recovery_no_wall / wp.harm_rate
  have hrpc : p_reactive_critical wp = wp.recovery_no_wall / wp.harm_rate := rfl
  linarith [hrpc]

/-! ## Optimal Threshold Theorem -/

/-- p_reactive_critical is the maximum threshold that covers the full dominance zone.
    Any θ > p_reactive_critical has a point in the dominance zone with p < θ,
    contradicting full coverage (p > θ for all p in zone). -/
theorem optimal_theta_is_p_reactive_critical (wp : WallParams) :
    ∀ θ : ℝ, (∀ p : ℝ, in_dominance_zone p wp → p > θ) → θ ≤ p_reactive_critical wp := by
  intro θ hcover
  by_contra h
  push Not at h  -- h : p_reactive_critical wp < θ (negation of θ ≤ p_reactive_critical)
  have henv := proactive_extends_envelope wp  -- p_reactive < p_proactive
  -- Split: θ is below or above p_proactive_critical
  rcases lt_or_ge θ (p_proactive_critical wp) with hlt | hge
  · -- θ < p_proactive_critical: midpoint (p_reactive, θ) is in dominance zone and < θ
    have pmid_in : in_dominance_zone ((p_reactive_critical wp + θ) / 2) wp :=
      ⟨by linarith, by linarith⟩
    -- hcover gives midpoint > θ, but midpoint < θ — contradiction
    linarith [hcover _ pmid_in]
  · -- θ ≥ p_proactive_critical: midpoint of dominance zone is < p_proactive ≤ θ
    have pmid_in : in_dominance_zone ((p_reactive_critical wp + p_proactive_critical wp) / 2) wp :=
      ⟨by linarith, by linarith⟩
    -- hcover gives midpoint > θ, but midpoint < p_proactive ≤ θ — contradiction
    linarith [hcover _ pmid_in, pmid_in.2]

/-! ## Dominance Zone Width -/

/-- The width of the proactive dominance zone = (r₁ - r₀) / harm_rate.
    Wider recovery improvement → more room for proactive wall above reactive boundary. -/
theorem dominance_zone_width (wp : WallParams) :
    p_proactive_critical wp - p_reactive_critical wp =
    (wp.recovery_wall - wp.recovery_no_wall) / wp.harm_rate := by
  unfold p_proactive_critical p_reactive_critical
  rw [← sub_div]

/-- Greater recovery improvement (r₁ - r₀) yields a wider dominance zone
    (when harm_rate is equal). More L3 blocking benefit → more resilient architecture. -/
theorem wider_recovery_gap_extends_zone (wp₁ wp₂ : WallParams)
    (h_harm : wp₁.harm_rate = wp₂.harm_rate)
    (h_rec : wp₁.recovery_wall - wp₁.recovery_no_wall <
             wp₂.recovery_wall - wp₂.recovery_no_wall) :
    p_proactive_critical wp₁ - p_reactive_critical wp₁ <
    p_proactive_critical wp₂ - p_reactive_critical wp₂ := by
  calc p_proactive_critical wp₁ - p_reactive_critical wp₁
      = (wp₁.recovery_wall - wp₁.recovery_no_wall) / wp₁.harm_rate := dominance_zone_width wp₁
    _ = (wp₁.recovery_wall - wp₁.recovery_no_wall) / wp₂.harm_rate := by rw [h_harm]
    _ < (wp₂.recovery_wall - wp₂.recovery_no_wall) / wp₂.harm_rate :=
        div_lt_div_of_pos_right h_rec wp₂.harm_pos
    _ = p_proactive_critical wp₂ - p_reactive_critical wp₂ := (dominance_zone_width wp₂).symm

end OptimalTheta

end
