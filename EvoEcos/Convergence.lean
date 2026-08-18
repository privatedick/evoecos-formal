/-
Convergence Criterion
=====================

"A system that can no longer reduce its error structure under varied exposure
has converged to a compact representation of the data-generating process."

Formalized: If L1 stability remains above the wall deactivation threshold
under all bounded perturbations, then L3 has converged and can always plan
autonomously (the wall can come down).

This gives a principled answer to "when can the wall come down?":
exactly when the system's robustness margin exceeds the maximum expected
perturbation.

Connection to experiments:
  - CartPole/Acrobot: wall helps at moderate noise, converges at low noise
  - LunarLander: wall helps at moderate noise, L1 false-trigger cost at high
  - MountainCar/MuJoCo: L1 not viable, convergence impossible via wall
  - False-positive-rate principle: convergence requires low false-positive rate
-/

import EvoEcos.Layers
import Mathlib.Data.Real.Basic

noncomputable section

namespace EvoEcos

/-! ## Perturbation Model -/

/-- A bounded perturbation parameterized by magnitude ε ≥ 0. -/
structure Perturbation where
  ε : ℝ
  hε : ε ≥ 0

namespace Perturbation

/-- Apply perturbation to L1 stability (worst-case: reduces by ε, clamped to 0) -/
def applyToStability (p : Perturbation) (s : Probability) : Probability :=
  ⟨max 0 (s.val - p.ε),
    by
      constructor
      · exact le_max_left 0 (s.val - p.ε)
      · have h_sub : s.val - p.ε ≤ s.val := by linarith [p.hε]
        have h_max : max 0 (s.val - p.ε) ≤ s.val :=
          max_le s.property.1 h_sub
        exact le_trans h_max s.property.2⟩

/-- Apply perturbation to system state (affects L1 stability only) -/
def apply (p : Perturbation) (s : SystemState) : SystemState :=
  { s with l1 := { s.l1 with stability := p.applyToStability s.l1.stability } }

end Perturbation

/-! ## Definitions -/

/-- Robustness margin: distance from stability to wall deactivation threshold -/
def RobustnessMargin (s : SystemState) : ℝ :=
  s.l1.stability.val - 0.6

/-- Converged under perturbation ε: stability stays above threshold after ε -/
def IsConvergedUnder (s : SystemState) (ε : ℝ) : Prop :=
  ε ≥ 0 → s.l1.stability.val - ε > 0.6

/-- Fully converged: positive robustness margin (stability > 0.6) -/
def IsConverged (s : SystemState) : Prop :=
  RobustnessMargin s > 0

/-- Convergence threshold: wall deactivation boundary -/
def ConvergenceThreshold : ℝ := 0.6

/-- Convergence gap: learning remaining before wall can come down -/
def ConvergenceGap (s : SystemState) : ℝ :=
  ConvergenceThreshold - s.l1.stability.val

/-! ## Basic Equivalences -/

theorem converged_iff : ∀ s, IsConverged s ↔ s.l1.stability.val > 0.6 := by
  intro s
  simp only [IsConverged, RobustnessMargin]
  constructor
  · intro h; exact sub_pos.mp h
  · intro h; exact sub_pos.mpr h

theorem margin_nonneg_iff : ∀ s, RobustnessMargin s ≥ 0 ↔ s.l1.stability.val ≥ 0.6 := by
  intro s
  simp only [RobustnessMargin]
  constructor
  · intro h; exact le_of_sub_nonneg h
  · intro h; exact sub_nonneg.mpr h

/-- Convergence under ε implies convergence under smaller perturbations -/
theorem converged_monotone (s : SystemState) (ε₁ ε₂ : ℝ)
    (h₁₂ : ε₁ ≤ ε₂) (h_conv : IsConvergedUnder s ε₂) :
    IsConvergedUnder s ε₁ := by
  intro hε₁
  have h := h_conv (by linarith)
  linarith

/-! ## Core: Perturbed Stability -/

/-- Converged under perturbation ⟹ perturbed stability > 0.6 -/
theorem converged_perturbed_stability
    (s : SystemState) (p : Perturbation)
    (h_conv : IsConvergedUnder s p.ε) :
    (Perturbation.apply p s).l1.stability.val > 0.6 := by
  have h := h_conv p.hε
  unfold Perturbation.apply Perturbation.applyToStability
  show max 0 (s.l1.stability.val - p.ε) > 0.6
  have h_pos : 0 ≤ s.l1.stability.val - p.ε := by
    calc s.l1.stability.val - p.ε ≥ 0.6 := by linarith
      _ ≥ 0 := by norm_num
  rw [max_eq_right h_pos]
  exact h

/-! ## Convergence ⟹ Wall Deactivation -/

/-- Converged ⟹ wall deactivates on perturbed state -/
theorem convergence_wall_false
    (s : SystemState) (p : Perturbation)
    (h_conv : IsConvergedUnder s p.ε) :
    (L2State.deactivateWall s.l2 (Perturbation.apply p s).l1).wall = false := by
  have h := converged_perturbed_stability s p h_conv
  unfold L2State.deactivateWall
  split
  · rfl
  · contradiction

/-! ## Convergence ⟹ L1 Safety Preserved -/

/-- Converged ⟹ noCollapse preserved (stability > 0.6 > 0) -/
theorem convergence_noCollapse
    (s : SystemState) (p : Perturbation)
    (h_conv : IsConvergedUnder s p.ε) :
    L1State.noCollapse (Perturbation.apply p s).l1 := by
  have h := converged_perturbed_stability s p h_conv
  unfold L1State.noCollapse
  exact lt_trans (by norm_num : (0 : ℝ) < 0.6) h

/-! ## Non-Convergence ⟹ Wall Still Needed -/

/-- Stability ≤ 0.6 ⟹ not converged -/
theorem not_converged_low_stability
    (s : SystemState) (h : s.l1.stability.val ≤ 0.6) :
    ¬IsConverged s := by
  intro hc
  have := (converged_iff s).mp hc
  linarith

/-! ## Convergence Gap -/

theorem gap_at_threshold (s : SystemState) (h : s.l1.stability.val = 0.6) :
    ConvergenceGap s = 0 := by
  unfold ConvergenceGap ConvergenceThreshold; linarith

theorem gap_negative_converged (s : SystemState) (h : IsConverged s) :
    ConvergenceGap s < 0 := by
  unfold ConvergenceGap ConvergenceThreshold
  have := (converged_iff s).mp h
  linarith

/-! ## Main Theorem: The Convergence Criterion -/

/-- **The Convergence Criterion.**
    Given a system converged under perturbation p, if L3 is unblocked,
    then L3 can plan autonomously with the wall deactivated.

    Formalizes: "a system that can no longer reduce its error structure
    under varied exposure has converged to a compact representation." -/
theorem convergence_criterion
    (s : SystemState) (p : Perturbation)
    (h_conv : IsConvergedUnder s p.ε)
    (h_l3_active : s.l3.active = true)
    (h_l3_unblocked : s.l3.blocked = false) :
    -- (1) L3 can plan after wall deactivation
    L3State.canPlan s.l3
      (L2State.deactivateWall s.l2 (Perturbation.apply p s).l1) ∧
    -- (2) Wall is inactive after perturbation
    (L2State.deactivateWall s.l2 (Perturbation.apply p s).l1).wall = false ∧
    -- (3) L1 safety preserved
    L1State.noCollapse (Perturbation.apply p s).l1 := by
  have h_wall := convergence_wall_false s p h_conv
  refine ⟨?_, h_wall, convergence_noCollapse s p h_conv⟩
  -- L3 can plan: active ∧ ¬blocked ∧ ¬wall
  unfold L3State.canPlan
  refine ⟨h_l3_active, ?_, ?_⟩
  · -- ¬blocked
    intro h_bt; rw [h_l3_unblocked] at h_bt; exact Bool.false_ne_true h_bt
  · -- ¬wall
    intro h_wt; rw [h_wall] at h_wt; exact Bool.false_ne_true h_wt

/-! ## Convergence Preservation under Non-L1 Transitions -/

/-- A transition affects L1 iff it is one of the three L1 actions. -/
def Transition.TransKind.affectsL1 : Transition.TransKind → Prop
  | Transition.TransKind.L1ReflexAction => True
  | Transition.TransKind.L1HeuristicAction => True
  | Transition.TransKind.L1MaintainStability => True
  | _ => False

/-- **Convergence is preserved by any non-L1 transition.**
    If s1 is converged (stability > 0.6) and s1 → s2 is a valid step whose
    transition kind does not touch L1, then s2 is also converged.
    Proof: each non-L1 case in `isValidStep` sets `s2 = { s1 with l2/l3/l4 := ... }`
    (or `s2 = s1` for Stutter), leaving `s1.l1 = s2.l1` by construction. -/
theorem convergence_preserved_by_nonL1_transition
    (s1 s2 : SystemState) (t : Transition.TransKind)
    (h_step : Transition.isValidStep { before := s1, after := s2, transition := t })
    (h_nonL1 : ¬ t.affectsL1)
    (h_conv : IsConverged s1) :
    IsConverged s2 := by
  -- Reduce IsConverged to stability comparison
  simp only [IsConverged, RobustnessMargin] at h_conv ⊢
  -- It suffices to show s2.l1 = s1.l1
  suffices h_l1_eq : s2.l1 = s1.l1 by rw [h_l1_eq]; exact h_conv
  cases t with
  | L1ReflexAction => exact absurd trivial h_nonL1
  | L1HeuristicAction => exact absurd trivial h_nonL1
  | L1MaintainStability => exact absurd trivial h_nonL1
  | L2UpdateBeliefs =>
      simp only [Transition.isValidStep] at h_step; simp [h_step]
  | L2ActivateWall =>
      simp only [Transition.isValidStep] at h_step; simp [h_step]
  | L2DeactivateWall =>
      simp only [Transition.isValidStep] at h_step; simp [h_step]
  | L3Plan =>
      simp only [Transition.isValidStep] at h_step; simp [h_step]
  | L3BlockWhenWallActive =>
      simp only [Transition.isValidStep] at h_step; simp [h_step]
  | L3Transmit =>
      simp only [Transition.isValidStep] at h_step; simp [h_step]
  | L3Ping =>
      simp only [Transition.isValidStep] at h_step; simp [h_step]
  | L4Observe =>
      simp only [Transition.isValidStep] at h_step; simp [h_step]
  | L4AdaptDown =>
      simp only [Transition.isValidStep] at h_step; simp [h_step]
  | Stutter =>
      simp only [Transition.isValidStep] at h_step; simp [h_step]

/-! ## L1 Filter Parameterization

Captures the empirical finding that L1 controller design (hysteresis, wider thresholds)
*attenuates* the effective perturbation on stability. A sharp L1 uses the identity
filter (ε passes through unchanged), while a well-designed L1 attenuates ε toward 0.
-/

/-- L1 filter: attenuates raw perturbation to effective degradation. -/
structure L1Filter where
  attenuate : ℝ → ℝ
  nonneg : ∀ ε : ℝ, 0 ≤ attenuate ε
  bounded : ∀ ε : ℝ, ε ≥ 0 → attenuate ε ≤ ε

namespace L1Filter

/-- Identity filter: no attenuation, models sharp L1. Clamps negatives to 0 so
    `attenuate ε = max 0 ε`, which equals ε for all ε ≥ 0 (the Perturbation domain). -/
def identity : L1Filter where
  attenuate ε := max 0 ε
  nonneg := by intro ε; exact le_max_left 0 ε
  bounded := by
    intro ε hε
    show max 0 ε ≤ ε
    rw [max_eq_right hε]

/-- Zero filter: perfect attenuation, models ideal hysteresis. -/
def zero : L1Filter where
  attenuate _ := 0
  nonneg := by intro _; exact le_refl 0
  bounded := by intro _ hε; exact hε

end L1Filter

namespace Perturbation

/-- Apply perturbation through an L1 filter. -/
def applyFiltered (p : Perturbation) (f : L1Filter)
    (s : SystemState) : SystemState :=
  { s with l1 := { s.l1 with stability :=
      ⟨max 0 (s.l1.stability.val - f.attenuate p.ε),
        by
          constructor
          · exact le_max_left 0 (s.l1.stability.val - f.attenuate p.ε)
          · have h_att : f.attenuate p.ε ≥ 0 := f.nonneg p.ε
            have h_sub : s.l1.stability.val - f.attenuate p.ε ≤ s.l1.stability.val :=
              by linarith
            have h_max : max 0 (s.l1.stability.val - f.attenuate p.ε)
                ≤ s.l1.stability.val :=
              max_le s.l1.stability.property.1 h_sub
            exact le_trans h_max s.l1.stability.property.2⟩ } }

/-- Converged under filtered perturbation ⟹ perturbed stability > 0.6 -/
theorem convergence_under_l1_filter
    (s : SystemState) (p : Perturbation) (f : L1Filter)
    (h_conv : IsConvergedUnder s (f.attenuate p.ε)) :
    (Perturbation.applyFiltered p f s).l1.stability.val > 0.6 := by
  have h_att : f.attenuate p.ε ≥ 0 := f.nonneg p.ε
  have h := h_conv h_att
  unfold Perturbation.applyFiltered
  show max 0 (s.l1.stability.val - f.attenuate p.ε) > 0.6
  have h_pos : 0 ≤ s.l1.stability.val - f.attenuate p.ε := by
    calc s.l1.stability.val - f.attenuate p.ε ≥ 0.6 := by linarith
      _ ≥ 0 := by norm_num
  rw [max_eq_right h_pos]
  exact h

/-- Identity-filter case recovers the original Perturbation.apply. -/
theorem convergence_identity_filter_equiv (s : SystemState) (p : Perturbation) :
    Perturbation.applyFiltered p L1Filter.identity s = Perturbation.apply p s := by
  simp only [Perturbation.applyFiltered, Perturbation.apply,
    Perturbation.applyToStability, L1Filter.identity]
  congr 1
  -- Stability field: show the Probability proofs are equal after rewriting
  simp only [max_eq_right p.hε]

end Perturbation

end EvoEcos

end
