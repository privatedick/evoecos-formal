/-
L1 Energy Sufficiency
=====================

Physical substrate for the NoCollapse invariant: L1's energy budget
must remain positive for stability to be maintained.

Parameters match src/stable_bootstrap_arch.py:
  ENERGY_INTAKE_RATE = 0.1, HOMEOSTATIC_COST = 0.02, STRESS_COST_COEFF = 0.1
  REFLEX_ENERGY_COST = 0.05, MAX_ENERGY = 1.0, ENERGY_CRITICAL_THRESH = 0.1

Composes with:
  - NoStrangeAttractor.stress_iter_bound (stress decay 0.95^n)
  - Layers.L1State.noCollapse (stability > 0)

Downstream consumer: L1.act() runtime (maintain_energy_budget), iteration 49.
-/

import EvoEcos.Types
import EvoEcos.Layers
import Mathlib.Data.Real.Basic

noncomputable section

namespace EvoEcos

/-! ## Energy Budget Parameters -/

def energyIntakeRate : ℝ := 10 / 100
def homeostaticCost : ℝ := 2 / 100
def stressCostCoeff : ℝ := 10 / 100
def reflexEnergyCost : ℝ := 5 / 100
def energyCriticalThreshold : ℝ := 10 / 100

namespace L1State

/-- Total homeostatic cost: baseline + stress-proportional. -/
def homeostaticTotal (s : L1State) : ℝ :=
  homeostaticCost + stressCostCoeff * s.stress.val

/-- Energy deficit: energy below critical threshold. -/
def energyDeficit (s : L1State) : Prop :=
  s.energy.val < energyCriticalThreshold

/-! ## Parameter Lemmas -/

theorem intake_positive : (0 : ℝ) < energyIntakeRate := by
  unfold energyIntakeRate; norm_num

theorem homeostatic_positive : (0 : ℝ) < homeostaticCost := by
  unfold homeostaticCost; norm_num

theorem reflex_cost_positive : (0 : ℝ) < reflexEnergyCost := by
  unfold reflexEnergyCost; norm_num

theorem critical_threshold_positive : (0 : ℝ) < energyCriticalThreshold := by
  unfold energyCriticalThreshold; norm_num

/-- Stress cost component is non-negative. -/
theorem stress_cost_nonneg (s : L1State) : (0 : ℝ) ≤ 10 / 100 * s.stress.val :=
  mul_nonneg (by norm_num) s.stress.property.1

/-- Homeostatic total is always positive. -/
theorem homeostatic_total_positive (s : L1State) :
    (0 : ℝ) < 2 / 100 + 10 / 100 * s.stress.val := by
  have : (0 : ℝ) ≤ 10 / 100 * s.stress.val := stress_cost_nonneg s
  linarith

/-! ## Balance Theorems -/

/-- At low stress without reflex, intake exceeds homeostatic cost.
    This is the sufficiency condition: E_in > E_base + c·σ when σ < 0.3. -/
theorem balance_positive_low_stress (s : L1State) (h_stress : s.stress.val < 3 / 10) :
    (0 : ℝ) < 10 / 100 - (2 / 100 + 10 / 100 * s.stress.val) := by
  -- 10/100 - (2/100 + 10/100 * σ) = 8/100 - 10/100 * σ
  -- Since σ < 3/10: 10/100 * σ < 3/100, so result > 8/100 - 3/100 = 5/100 > 0
  have h_bound : (10 / 100 : ℝ) * s.stress.val < 3 / 100 :=
    calc (10 / 100) * s.stress.val
        < (10 / 100) * (3 / 10) := mul_lt_mul_of_pos_left h_stress (by norm_num)
      _ = 3 / 100 := by norm_num
  linarith

/-- At high stress with reflex, balance is non-positive (deficit mode).
    E_in - (E_homeostatic + E_reflex) ≤ 0 when σ ≥ 0.3.
    Equality at σ = 0.3 exactly. -/
theorem balance_nonpos_high_stress_reflex (s : L1State)
    (h_stress : s.stress.val ≥ 3 / 10) :
    (10 : ℝ) / 100 - (2 / 100 + 10 / 100 * s.stress.val + 5 / 100) ≤ 0 := by
  -- 10/100 - (7/100 + 10/100 * σ) = 3/100 - 10/100 * σ
  -- Since σ ≥ 3/10: 10/100 * σ ≥ 3/100, so result ≤ 0
  have h_bound : (10 / 100 : ℝ) * s.stress.val ≥ 3 / 100 :=
    calc (10 / 100) * s.stress.val
        ≥ (10 / 100) * (3 / 10) := mul_le_mul_of_nonneg_left h_stress (by norm_num)
      _ = 3 / 100 := by norm_num
  linarith

/-! ## Energy Bounds (from Probability type) -/

theorem energy_nonneg (s : L1State) : (0 : ℝ) ≤ s.energy.val :=
  s.energy.property.1

theorem energy_le_one (s : L1State) : s.energy.val ≤ 1 :=
  s.energy.property.2

/-! ## Bridge to NoCollapse -/

/-- Initial state has noCollapse (stability = 1 > 0). -/
theorem init_noCollapse : L1State.init.noCollapse := by
  unfold L1State.noCollapse L1State.init
  simp only [Probability.one]
  norm_num

/-- Initial state has no energy deficit (energy = 1 > threshold). -/
theorem init_no_deficit : ¬L1State.init.energyDeficit := by
  unfold energyDeficit energyCriticalThreshold L1State.init
  simp only [Probability.one]
  norm_num

/-- Deficit iff energy below threshold. -/
theorem deficit_iff_below_threshold (s : L1State) :
    s.energyDeficit ↔ s.energy.val < 10 / 100 := by
  unfold energyDeficit energyCriticalThreshold; rfl

/-- At threshold exactly, not in deficit. -/
theorem at_threshold_not_deficit (s : L1State)
    (h : s.energy.val = energyCriticalThreshold) :
    ¬s.energyDeficit := by
  unfold energyDeficit energyCriticalThreshold at *
  intro h_def
  linarith

end L1State

/-! ## Parameter Equality Lemmas -/

@[simp] theorem energyIntakeRate_eq : energyIntakeRate = 10 / 100 := rfl
@[simp] theorem homeostaticCost_eq : homeostaticCost = 2 / 100 := rfl
@[simp] theorem stressCostCoeff_eq : stressCostCoeff = 10 / 100 := rfl
@[simp] theorem reflexEnergyCost_eq : reflexEnergyCost = 5 / 100 := rfl
@[simp] theorem energyCriticalThreshold_eq : energyCriticalThreshold = 10 / 100 := rfl

end EvoEcos
