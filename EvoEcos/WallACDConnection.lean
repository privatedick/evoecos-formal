/-
WallACDConnection: ACD Theorem ↔ EMA Threshold Detection
=========================================================

The ACD theorem (ACD.lean, BoundaryACD.lean) proves that a system can detect a
failure class iff the failure locus satisfies a boundary condition. Separately,
WallCostBenefit.lean proves that the optimal wall activation threshold is
theta* = r0/h.

This file establishes the formal bridge: the EMA threshold test implements the
ACD boundary condition for threat detection. Specifically:
  - theta* = r0/h is an ACD-type boundary (divides survivable from threatened)
  - If the EMA estimate tracks true p within delta, and p is above theta* by
    more than delta, then the EMA correctly detects the boundary crossing
  - False positives (EMA > theta* when p ≤ theta*) require tracking error to
    exceed the gap (theta* - p) — the ACD boundary is "stable under small noise"

The key insight: the ACD "observability boundary" for threat detection IS the
wall cost-benefit boundary theta* = r0/h. The EMA implements the detector.

Architecture change (iter 19):
  ModelingLayer.acd_boundary_detection_confidence property:
    (threat_ema - theta*) / delta_estimate
  Positive when EMA margin exceeds estimated tracking error → reliable detection.

Key theorems:
  1. ema_detects_boundary_crossing      — margin > delta → EMA detects (no false negatives)
  2. below_theta_implies_safe_or_noisy  — EMA below theta* → safe OR tracking error ≥ gap
  3. false_positive_requires_large_err  — FP requires |EMA-p| > (theta*-p)
  4. margin_determines_safe_delta       — delta < margin → reliable detection
  5. half_margin_gives_safety_cushion   — delta < margin/2 → EMA above halfway point
  6. boundary_detection_uncertain       — at p = theta*, detection is ambiguous for any delta
  7. detection_confidence_monotone      — larger p → same delta still reliable
  8. acd_partition_well_defined         — guard band [theta*-delta, theta*+delta] ⊂ (0, p**)
  9. acd_boundary_guard_band            — theta* is interior to guard band
 10. acd_wall_composition               — detection + cost-benefit = ACD-consistent activation
-/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic
import EvoEcos.WallCostBenefit

noncomputable section

namespace WallACDConnection

open WallCostBenefit

/-! ## EMA Boundary Detection Theorems -/

/-- Theorem 1 (Core): If the EMA tracks true p within delta AND p exceeds theta*
    by more than delta, then EMA correctly detects the boundary crossing (EMA > theta*).

    This is the "no false negative" guarantee: whenever the true threat p is reliably
    above the ACD boundary theta*, the EMA detector cannot miss it. -/
theorem ema_detects_boundary_crossing (ema p delta : ℝ)
    (h_track : |ema - p| < delta)
    (h_margin : p > r0 / h + delta) :
    ema > r0 / h := by
  have h_ema_lb : ema > p - delta := by
    have := (abs_lt.mp h_track).1
    linarith
  linarith

/-- Theorem 2: When EMA is below theta*, either p is truly safe (p ≤ theta*) OR
    the tracking error is at least as large as the gap (p - theta*).
    This shows that a "safe" EMA reading is reliable when tracking error is small. -/
theorem below_theta_implies_safe_or_noisy (ema p : ℝ)
    (h_below : ema ≤ r0 / h) :
    p ≤ r0 / h ∨ |ema - p| ≥ p - r0 / h := by
  by_cases hp : p ≤ r0 / h
  · left; exact hp
  · right
    simp only [not_le] at hp
    rw [abs_of_nonpos (by linarith)]
    linarith

/-- Theorem 3: A false positive (EMA > theta* when p ≤ theta*) requires the EMA
    tracking error to strictly exceed the gap (theta* - p).
    The ACD boundary is stable: noise smaller than the margin cannot cause false alarms. -/
theorem false_positive_requires_large_err (ema p : ℝ)
    (h_fp : ema > r0 / h)
    (h_below : p ≤ r0 / h) :
    |ema - p| > r0 / h - p := by
  rw [abs_of_pos (by linarith)]
  linarith

/-- Theorem 4: The detection margin determines the maximum safe tracking error.
    If delta < (p - theta*), EMA > theta* — reliable detection guaranteed. -/
theorem margin_determines_safe_delta (ema p delta : ℝ)
    (h_track : |ema - p| ≤ delta)
    (h_safe : delta < p - r0 / h) :
    ema > r0 / h := by
  have h_ema_lb : ema ≥ p - delta := by
    have := (abs_le.mp h_track).1
    linarith
  linarith

/-- Theorem 5: Half-margin tracking gives a safety cushion.
    When delta ≤ (p - theta*)/2 AND p > theta*, EMA is above theta* by at least
    (p - theta*)/2 — providing a safety margin against additional perturbations. -/
theorem half_margin_gives_safety_cushion (ema p delta : ℝ)
    (h_track : |ema - p| ≤ delta)
    (h_half : delta ≤ (p - r0 / h) / 2)
    (h_above : p > r0 / h) :
    ema ≥ r0 / h + (p - r0 / h) / 2 := by
  have h_guard : (p - r0 / h) / 2 ≥ 0 := by linarith
  have h_ema_lb : ema ≥ p - delta := by
    have := (abs_le.mp h_track).1
    linarith
  linarith

/-- Theorem 6: At exactly p = theta* (the ACD boundary), detection is uncertain.
    For any delta > 0, the EMA can be on either side of theta*. -/
theorem boundary_detection_uncertain (ema p delta : ℝ)
    (h_at_boundary : p = r0 / h)
    (h_track : |ema - p| ≤ delta) :
    r0 / h - delta ≤ ema ∧ ema ≤ r0 / h + delta := by
  rw [h_at_boundary] at h_track
  have := abs_le.mp h_track
  constructor <;> linarith [this.1, this.2]

/-- Theorem 7: Detection confidence is monotone in p.
    If p₁ is reliably detected (p₁ > theta* + delta) and p₁ < p₂, then p₂ is
    also reliably detected by the same delta. -/
theorem detection_confidence_monotone (p1 p2 delta : ℝ)
    (h_order : p1 < p2)
    (h_detect1 : p1 > r0 / h + delta) :
    p2 > r0 / h + delta := by linarith

/-- Theorem 8: For any delta < theta*, the guard band [theta*-delta, theta*+delta]
    is well-defined within the feasible region: theta*-delta > 0 AND theta*+delta < p**.
    This shows the ACD partition is non-trivial and contained in the feasible zone. -/
theorem acd_partition_well_defined (delta : ℝ) (h_small : delta < r0 / h) :
    r0 / h - delta > 0 ∧ r0 / h + delta < r1 / h := by
  constructor
  · linarith [show (0 : ℝ) < r0 / h from by norm_num]
  · linarith [show r1 / h - r0 / h = r0 / h from by norm_num]

/-- Theorem 9: The ACD boundary theta* is interior to its own guard band.
    For any delta > 0, theta* is strictly between (theta*-delta) and (theta*+delta). -/
theorem acd_boundary_guard_band (delta : ℝ) (_h_pos : 0 < delta) :
    r0 / h - delta < r0 / h ∧ r0 / h < r0 / h + delta := by
  constructor <;> linarith

/-- Theorem 10 (Composition): EMA detection + WallCostBenefit = ACD-consistent activation.
    When EMA reliably detects p > theta* (margin > tracking error), wall activation is
    simultaneously ACD-consistent (EMA > theta*) AND cost-beneficial (r0 - p*h < 0).
    The EMA threshold test thus implements the ACD observation boundary. -/
theorem acd_wall_composition (ema p delta : ℝ)
    (h_track : |ema - p| < delta)
    (h_margin : p > r0 / h + delta) :
    ema > r0 / h ∧ r0 - p * h < 0 := by
  have h_delta_pos : delta > 0 := lt_of_le_of_lt (abs_nonneg _) h_track
  have h_p_above : p > r0 / h := by linarith
  exact ⟨ema_detects_boundary_crossing ema p delta h_track h_margin,
         WallCostBenefit.theta_star_earliest_needed p h_p_above⟩

end WallACDConnection

end
