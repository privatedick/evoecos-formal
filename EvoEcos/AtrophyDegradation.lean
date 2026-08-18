/-
# L1 Atrophy and Graceful Degradation Theorems

**Date:** 2026-05-09

## Summary

Two theorems formalizing experimentally confirmed ACD(i) properties:

1. **L1 Atrophy Without Wall**: When the wall is absent, L1 quality decays.
   Experiment: l1_atrophy (CONFIRMED)

2. **Graceful Degradation**: Removing higher layers causes bounded loss.
   Experiment: BQ_graceful_degradation (CONFIRMED)

## What this file proves (target: 0 sorry)

* `l1_atrophy_without_wall` — quality decays without wall
* `l1_atrophy_prevented_by_wall` — wall preserves quality
* `degradation_l3_bounded` — L3 removal ≤ 20% absolute
* `degradation_l2_l3_bounded` — L2+L3 removal ≤ 50% absolute
* `no_collapse_under_degradation` — L1 never collapses
-/

import EvoEcos.Layers
import EvoEcos.Invariants

noncomputable section

namespace EvoEcos

/-! ## Interference Model -/

/-- Interference rate per step when wall absent. Zero when wall present. -/
def interference (l3 : L3State) (wallActive : Bool) : ℝ :=
  if wallActive then 0 else l3.understanding.val / 100

theorem interference_nonneg (l3 : L3State) (w : Bool) : 0 ≤ interference l3 w := by
  simp only [interference]
  split
  · norm_num
  · have := l3.understanding.property.1
    exact div_nonneg this (by norm_num)

theorem interference_zero_walled (l3 : L3State) : interference l3 true = 0 := by
  simp [interference]

theorem interference_pos_unwalled (l3 : L3State) (h : (0 : ℝ) < l3.understanding.val) :
    (0 : ℝ) < interference l3 false := by
  simp only [interference]
  exact div_pos h (by norm_num : (0 : ℝ) < (100 : ℝ))

/-! ## Quality After N Steps -/

/-- Quality after n steps: initial quality minus accumulated interference. -/
def qualityAfterN (init : ℝ) (interf : ℝ) (n : Nat) : ℝ :=
  init - n * interf

theorem quality_decreases_each_step (init interf : ℝ) (h_interf : 0 < interf) (n : Nat) :
    qualityAfterN init interf (n + 1) < qualityAfterN init interf n := by
  simp only [qualityAfterN, Nat.cast_succ]
  linarith

/-- **L1 Atrophy Without Wall**: Quality strictly decreases each step
    when wall absent and L3 has nonzero understanding. -/
theorem l1_atrophy_without_wall (l1 : L1State) (l3 : L3State)
    (h_active : (0 : ℝ) < l3.understanding.val) (n : Nat) :
    qualityAfterN l1.stability.val (interference l3 false) (n + 1) <
    qualityAfterN l1.stability.val (interference l3 false) n :=
  quality_decreases_each_step _ _ (interference_pos_unwalled l3 h_active) n

/-- **L1 Atrophy Prevented by Wall**: With wall active, interference = 0,
    so quality is exactly preserved. -/
theorem l1_atrophy_prevented_by_wall (l1 : L1State) (l3 : L3State) (n : Nat) :
    qualityAfterN l1.stability.val (interference l3 true) n = l1.stability.val := by
  simp [qualityAfterN, interference_zero_walled]

/-! ## Graceful Degradation -/

/-- Full system performance. Weights: L1=5, L2=3, L3=2 (scaled ×10). -/
def Perf10 (l1 : L1State) (l2 : L2State) (l3 : L3State) : ℝ :=
  5 * l1.stability.val + 3 * (1 - l2.uncertainty.val) + 2 * l3.understanding.val

/-- L1+L2 only (no L3). L1 weight absorbs L3's share: 5→7. -/
def Perf10NoL3 (l1 : L1State) (l2 : L2State) : ℝ :=
  7 * l1.stability.val + 3 * (1 - l2.uncertainty.val)

/-- L1 only. -/
def Perf10L1Only (l1 : L1State) : ℝ :=
  10 * l1.stability.val

/-- Helper: full - noL3 = 2*(u3.val - s1.val) -/
lemma diff_full_nol3_eq (l1 : L1State) (l2 : L2State) (l3 : L3State) :
    Perf10 l1 l2 l3 - Perf10NoL3 l1 l2 = 2 * (l3.understanding.val - l1.stability.val) := by
  simp only [Perf10, Perf10NoL3]
  ring

/-- **L3 removal ≤ 2 (= 20% of 10)**. -/
theorem degradation_l3_bounded (l1 : L1State) (l2 : L2State) (l3 : L3State) :
    Perf10 l1 l2 l3 - Perf10NoL3 l1 l2 ≤ 2 := by
  rw [diff_full_nol3_eq]
  have h_u := l3.understanding.property.2
  have h_s := l1.stability.property.1
  calc 2 * (l3.understanding.val - l1.stability.val)
      ≤ 2 * (1 - l1.stability.val) := by linarith
    _ ≤ 2 * 1 := by linarith
    _ ≤ 2 := by norm_num

/-- Helper: full - L1only. -/
lemma diff_full_l1only_eq (l1 : L1State) (l2 : L2State) (l3 : L3State) :
    Perf10 l1 l2 l3 - Perf10L1Only l1 =
    3 * (1 - l2.uncertainty.val) + 2 * l3.understanding.val - 5 * l1.stability.val := by
  simp only [Perf10, Perf10L1Only]
  ring

/-- **L2+L3 removal ≤ 5 (= 50% of 10)**. -/
theorem degradation_l2_l3_bounded (l1 : L1State) (l2 : L2State) (l3 : L3State) :
    Perf10 l1 l2 l3 - Perf10L1Only l1 ≤ 5 := by
  rw [diff_full_l1only_eq]
  have h_u := l2.uncertainty.property.1
  have h_v := l3.understanding.property.2
  have h_s := l1.stability.property.1
  calc 3 * (1 - l2.uncertainty.val) + 2 * l3.understanding.val - 5 * l1.stability.val
      ≤ 3 * 1 + 2 * l3.understanding.val - 5 * l1.stability.val := by linarith
    _ ≤ 3 * 1 + 2 * 1 - 5 * l1.stability.val := by linarith
    _ ≤ 3 * 1 + 2 * 1 - 5 * 0 := by linarith
    _ = 5 := by norm_num

/-- **No Collapse Under Degradation**: L1-only performance positive. -/
theorem no_collapse_under_degradation (l1 : L1State)
    (h : L1State.noCollapse l1) :
    (0 : ℝ) < Perf10L1Only l1 := by
  simp only [Perf10L1Only, L1State.noCollapse] at *
  exact mul_pos (by norm_num : (0 : ℝ) < 10) h

/-- Full system performance nonnegative. -/
theorem perf10_nonneg (l1 : L1State) (l2 : L2State) (l3 : L3State) :
    (0 : ℝ) ≤ Perf10 l1 l2 l3 := by
  simp only [Perf10]
  have h1 := l1.stability.property.1
  have h2 := l2.uncertainty.property.2
  have h3 := l3.understanding.property.1
  nlinarith

/-- L1-only performance nonnegative. -/
theorem perf10_l1only_nonneg (l1 : L1State) :
    (0 : ℝ) ≤ Perf10L1Only l1 := by
  simp only [Perf10L1Only]
  exact mul_nonneg (by norm_num) l1.stability.property.1

end EvoEcos
