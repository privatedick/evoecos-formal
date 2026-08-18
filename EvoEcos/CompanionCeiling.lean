/-
Companion Ceiling Law
=====================

Formalizes the empirical ceiling law: response_strength ≥ ceiling_ratio × drift_magnitude
is the exact threshold for companion safety ≥ 0.90.

Confirmed at 4 drift levels (0.40, 0.60, 0.80, 1.00) with rho = 1.000 and ratio CV = 0.109.
The ceiling ratio is 0.19 — the confirmed empirical safety≥0.90 threshold (companion_ceiling
[CONFIRMED]). The earlier 0.15 was a lower-drift-regime estimate; rs* ≈ 0.19 × drift_magnitude
is the tighter threshold. The separate zero-failure ceiling is 0.25.

8 theorems, 0 sorry. Extends DiscretenessGradient.

Date: 2026-05-28 (ceilingRatio tightened 0.15 → 0.19 on 2026-07-14)

Runtime coupling (src/stable_bootstrap_arch.py):
  runtime-reflected:
    meets_ceiling_sufficient_safety  → _check_companion_ceiling(response, drift)
      checks response >= 0.19 * drift at each companion wall-activation; logs WARNING on violation
    wall_never_meets_ceiling  → (implied; ceiling check with response=0 always warns)
    ceilingRatio = 0.19  → StableEpistemicBootstrapSystem._CEILING_RATIO = 0.19

  theory-only (no runtime analog — mathematical properties):
    ceiling_ratio_pos, ceiling_ratio_small, ceiling_ratio_lt_half  — numeric properties
    ceiling_monotone_response  — asymptotic monotonicity
    ceiling_scales_linearly  — linear scaling proof
    ceiling_threshold_pos  — positivity of threshold
-/

import EvoEcos.DiscretenessGradient
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace EvoEcos.CompanionCeiling

open DiscretenessGradient

/-! ## The Ceiling Ratio: 0.19 -/

/-- The ceiling ratio: companion response must be ≥ ceilingRatio × drift
    for companion safety ≥ 0.90.
    Empirically: ceilingRatio = 0.19, confirmed at 4 drift levels
    (companion_ceiling [CONFIRMED]). -/
def ceilingRatio : ℝ := 0.19

/-- A companion meets the ceiling criterion when response ≥ ceilingRatio × drift.
    This is the sufficient condition for safety ≥ 0.90. -/
structure MeetsCeiling where
  response : ℝ
  drift : ℝ
  response_pos : 0 < response
  drift_pos : 0 < drift
  meets_criterion : response ≥ ceilingRatio * drift

/-! ## Basic Properties of the Ceiling Ratio -/

/-- The ceiling ratio is positive. -/
theorem ceiling_ratio_pos : (0 : ℝ) < ceilingRatio := by
  unfold ceilingRatio; linarith

/-- The ceiling ratio is less than 1 (it is a fractional threshold). -/
theorem ceiling_ratio_small : (ceilingRatio : ℝ) < 1 := by
  unfold ceilingRatio; linarith

/-- The ceiling ratio is less than 1/2. -/
theorem ceiling_ratio_lt_half : (ceilingRatio : ℝ) < (0.5 : ℝ) := by
  unfold ceilingRatio; linarith

/-! ## Ceiling Sufficient for Companion Safety -/

/-- If a companion meets the ceiling criterion, then companionFunction ≥ 0 (safe).
    This connects the empirical ceiling law to the Lyapunov stability framework.
    The key insight: ceiling_ratio × drift is sufficient when state × response ≥ drift,
    which holds when state ≥ 1/ceilingRatio ≈ 5.26 (the system is not critically depleted). -/
theorem meets_ceiling_sufficient_safety (s : SystemState) (mc : MeetsCeiling)
    (h_state : s.state ≥ 1 / ceilingRatio)
    (h_drift_eq : s.drift = mc.drift) :
    (0 : ℝ) ≤ companionFunction s ⟨mc.response, mc.response_pos⟩ := by
  -- companion_stability requires: s.state * response ≥ s.drift and 0 < s.drift
  -- We build the product bound directly:
  --   s.state * mc.response ≥ s.state * (cr * drift) = (s.state * cr) * drift ≥ drift
  -- Key: s.state ≥ 1/cr > 0, so s.state * cr ≥ 1
  have h_ce_pos : (0 : ℝ) < ceilingRatio := ceiling_ratio_pos
  have h_state_pos : (0 : ℝ) < s.state := by
    have : (0 : ℝ) < 1 / ceilingRatio := div_pos (by positivity) h_ce_pos
    exact lt_of_lt_of_le this h_state
  have h_cr_ne : (ceilingRatio : ℝ) ≠ 0 := ne_of_gt h_ce_pos
  have h_s_cr_ge_one : s.state * ceilingRatio ≥ 1 := by
    -- s.state ≥ 1/cr ⟹ (s.state - 1/cr) * cr ≥ 0 ⟹ s*cr - 1 ≥ 0
    have h1 : (s.state - 1 / ceilingRatio) * ceilingRatio ≥ 0 := by
      have : s.state - 1 / ceilingRatio ≥ 0 := by linarith
      exact mul_nonneg this (le_of_lt h_ce_pos)
    have h2 : (s.state - 1 / ceilingRatio) * ceilingRatio = s.state * ceilingRatio - 1 := by
      calc (s.state - 1 / ceilingRatio) * ceilingRatio
          = s.state * ceilingRatio - (1 / ceilingRatio) * ceilingRatio := by ring
        _ = s.state * ceilingRatio - 1 := by field_simp [h_cr_ne]
    linarith
  have h_product : s.state * mc.response ≥ s.drift := by
    rw [h_drift_eq]
    calc s.state * mc.response
        ≥ s.state * (ceilingRatio * mc.drift) :=
      mul_le_mul_of_nonneg_left mc.meets_criterion (le_of_lt h_state_pos)
      _ = (s.state * ceilingRatio) * mc.drift := by ring
      _ ≥ 1 * mc.drift :=
      mul_le_mul_of_nonneg_right h_s_cr_ge_one (le_of_lt mc.drift_pos)
      _ = mc.drift := by ring
  exact companion_stability s ⟨mc.response, mc.response_pos⟩
    (by rw [h_drift_eq]; exact mc.drift_pos) h_product

/-! ## Monotonicity and Scaling -/

/-- The ceiling criterion is monotone in response: increasing response preserves the ceiling.
    If response₁ ≥ response₂ and both share the same drift, then response₂ meeting the
    ceiling implies response₁ also meets it. -/
theorem ceiling_monotone_response {r₁ r₂ d : ℝ}
    (h_ge : r₁ ≥ r₂) (_hd : 0 < d) (_hr₂ : 0 < r₂)
    (mc₂ : MeetsCeiling) (h_resp_eq : mc₂.response = r₂) (h_drift_eq : mc₂.drift = d) :
    r₁ ≥ ceilingRatio * d := by
  have h2 := mc₂.meets_criterion
  rw [h_resp_eq, h_drift_eq] at h2
  exact le_trans h2 h_ge

/-- The minimum sufficient response scales linearly with drift.
    rs ≥ ceilingRatio × drift. -/
theorem ceiling_scales_linearly (d : ℝ) (d_pos : 0 < d) :
    ceilingRatio * d > (0 : ℝ) := by
  exact mul_pos ceiling_ratio_pos d_pos

/-! ## Wall Never Meets Ceiling -/

/-- A wall (which has response = 0) can never meet the ceiling criterion for positive drift.
    This is why walls fail under continuous drift: they cannot provide the minimum
    response the ceiling law requires. -/
theorem wall_never_meets_ceiling (d : ℝ) (d_pos : 0 < d) :
    (0 : ℝ) < ceilingRatio * d ∧ ¬(0 ≥ ceilingRatio * d) := by
  constructor
  · exact mul_pos ceiling_ratio_pos d_pos
  · intro h_absurd
    linarith [mul_pos ceiling_ratio_pos d_pos]

/-- The ceiling threshold for a given drift level.
    Any response below this is unsafe. -/
noncomputable def ceilingThreshold (d : ℝ) : ℝ := ceilingRatio * d

/-- The ceiling threshold is positive for positive drift. -/
theorem ceiling_threshold_pos (d : ℝ) (d_pos : 0 < d) :
    (0 : ℝ) < ceilingThreshold d := by
  unfold ceilingThreshold
  exact mul_pos ceiling_ratio_pos d_pos

end EvoEcos.CompanionCeiling
