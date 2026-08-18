/-
L3 Affordability Certificate
============================

A resource-safety certificate for the L3 (understanding) layer's planning and
experimentation gates. L3 may only consume resources it can *afford*, and
affordability is defined so that spending never breaches L1's protected survival
reserve. This formalizes the runtime gates

    _can_afford_plan()        (UnderstandingLayer._can_afford_plan)
    _can_afford_experiment()  (UnderstandingLayer._can_afford_experiment)
    _estimate_plan_cost()     (UnderstandingLayer._estimate_plan_cost)

    All three live in stable_bootstrap_arch.py; referenced by method name rather
    than line number since these drift as the file grows (already drifted once,
    from :782 to :987 for _can_afford_experiment as of 2026-07-31).

whose docstring states the invariant verbatim: "KRITISK: Respektera
L1-stabilitet i budget" (respect L1 stability in the budget).

The discretionary energy L3 may draw is exactly the energy *above*
`energyCriticalThreshold` — the same reserve the energy-Lyapunov certificate
(`EnergyLyapunov`) shows is replenished by positive energy balance. So L1's
survival reserve is protected from both sides: replenished by the Lyapunov flow,
and never raided by L3.

Composes (does not re-prove):
  - EnergyLyapunov.energyBalance              (the sustainable-regime flow)
  - L1EnergySufficiency.energyCriticalThreshold / L1State.energyDeficit
  - L3Understanding: L3State.canExperiment / canPlan (capability gates)
  - Layers.wallActivateThreshold

Downstream consumer: _can_afford_plan() / _can_afford_experiment() live paths.
-/

import EvoEcos.Layers
import EvoEcos.L1EnergySufficiency
import EvoEcos.L3Understanding
import EvoEcos.EnergyLyapunov
import EvoEcos.NoStrangeAttractor
import Mathlib.Data.Real.Basic

noncomputable section

namespace EvoEcos.L3Affordability

/-! ## 1. Cost and budget model (mirrors the Python runtime) -/

/-- Discretionary energy L3 may consume: energy strictly above L1's protected
    survival reserve. L1's critical reserve is never available to L3. -/
def discretionaryEnergy (l1 : L1State) : ℝ := l1.energy.val - energyCriticalThreshold

/-- Plan cost = planningDepth × nSimulations × 0.1 (mirrors `_estimate_plan_cost`). -/
def planCost (depth nSims : Nat) : ℝ := (depth : ℝ) * (nSims : ℝ) * (1 / 10)

/-- Stability gate for experiments: `_can_afford_experiment` requires
    `stability_score > 0.5`. Note this is *stricter* than the wall-inactivity
    threshold (0.4): experiments demand more headroom than planning. -/
def experimentStabilityGate : ℝ := 1 / 2

/-- L3 can afford a plan of the given cost: the cost fits within the
    discretionary energy (the budget gate, independent of the wall/blocked
    capability gate). -/
def canAffordPlan (l1 : L1State) (cost : ℝ) : Prop :=
  0 ≤ cost ∧ cost ≤ discretionaryEnergy l1

/-- L3 can afford an experiment: cost fits the discretionary energy AND L1
    stability exceeds the (stricter) experiment gate. -/
def canAffordExperiment (l1 : L1State) (cost : ℝ) : Prop :=
  0 ≤ cost ∧ cost ≤ discretionaryEnergy l1 ∧ l1.stability.val > experimentStabilityGate

/-- Full plan-execution gate = capability (canPlan: active, unblocked, wall off)
    AND budget (canAffordPlan). -/
def canExecutePlan (l3 : L3State) (l1 : L1State) (l2 : L2State) (cost : ℝ) : Prop :=
  L3State.canPlan l3 l2 ∧ canAffordPlan l1 cost

/-- Full experiment-execution gate = capability AND budget. -/
def canExecuteExperiment (l3 : L3State) (l1 : L1State) (l2 : L2State) (cost : ℝ) : Prop :=
  L3State.canExperiment l3 l1 l2 ∧ canAffordExperiment l1 cost

/-! ## 2. Cost-model lemmas -/

/-- Plan cost is non-negative. -/
theorem planCost_nonneg (depth nSims : Nat) : 0 ≤ planCost depth nSims := by
  unfold planCost
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (by norm_num)

/-- Plan cost is monotone in planning depth (deeper plans cost more). -/
theorem planCost_mono_depth (d1 d2 nSims : Nat) (h : d1 ≤ d2) :
    planCost d1 nSims ≤ planCost d2 nSims := by
  unfold planCost
  have hd : (d1 : ℝ) ≤ (d2 : ℝ) := by exact_mod_cast h
  have hn : (0 : ℝ) ≤ (nSims : ℝ) := Nat.cast_nonneg _
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hd hn) (by norm_num)

/-! ## 3. The core safety property: affordability protects the L1 reserve -/

/-- **Reserve protection.** Executing any affordable plan leaves L1's energy at or
    above its critical survival reserve. This is the formal content of "respect
    L1 stability in the budget": L3 can never starve L1. -/
theorem afford_protects_reserve (l1 : L1State) (cost : ℝ)
    (h : canAffordPlan l1 cost) :
    l1.energy.val - cost ≥ energyCriticalThreshold := by
  obtain ⟨_, h_cost⟩ := h
  unfold discretionaryEnergy at h_cost
  linarith

/-- **Deficit blocks spending.** If L1 is in energy deficit, no plan with positive
    cost is affordable — discretionary energy is negative. -/
theorem deficit_blocks_afford (l1 : L1State) (cost : ℝ)
    (h_def : l1.energyDeficit) (h_pos : 0 < cost) :
    ¬canAffordPlan l1 cost := by
  intro h
  obtain ⟨_, h_cost⟩ := h
  unfold L1State.energyDeficit at h_def
  unfold discretionaryEnergy at h_cost
  linarith

/-- **Experiment affordability refines wall-safety.** Affording an experiment
    implies L1 stability is above the wall-activation threshold (since the
    experiment gate 0.5 strictly exceeds the wall threshold 0.4). -/
theorem experiment_afford_above_wall (l1 : L1State) (cost : ℝ)
    (h : canAffordExperiment l1 cost) :
    l1.stability.val > wallActivateThreshold := by
  obtain ⟨_, _, h_stab⟩ := h
  unfold experimentStabilityGate at h_stab
  unfold wallActivateThreshold
  linarith

/-! ## 4. Non-vacuity: a healthy L1 can afford real plans -/

/-- The initial (full-energy) L1 state can afford any plan costing up to 0.9
    (= 1 − reserve). The affordability gate is not vacuous. -/
theorem init_can_afford_plan (cost : ℝ) (h0 : 0 ≤ cost) (h1 : cost ≤ 9 / 10) :
    canAffordPlan L1State.init cost := by
  refine ⟨h0, ?_⟩
  have he : (L1State.init).energy.val = 1 := by simp [L1State.init, Probability.one]
  show cost ≤ discretionaryEnergy L1State.init
  unfold discretionaryEnergy energyCriticalThreshold
  rw [he]; linarith

/-! ## 5. Capstone: dual-axis experiment resource-safety -/

/-- **Experiment resource-safety certificate.** If L3 may execute an experiment
    (capability gate satisfied AND affordable), then it is safe on *both* axes:
    (1) L1 stability is at/above the wall threshold, (2) the wall is inactive,
    and (3) the experiment's energy cost leaves L1's survival reserve intact.
    A single gate discharges both the stability/wall safety and the energy
    safety of L3 resource consumption. -/
theorem experiment_resource_safety
    (l3 : L3State) (l1 : L1State) (l2 : L2State) (cost : ℝ)
    (h : canExecuteExperiment l3 l1 l2 cost) :
    l1.stability.val ≥ wallActivateThreshold
    ∧ ¬l2.wall
    ∧ l1.energy.val - cost ≥ energyCriticalThreshold := by
  obtain ⟨h_can, h_afford⟩ := h
  refine ⟨h_can.2.2.2, h_can.2.2.1, ?_⟩
  obtain ⟨_, h_cost, _⟩ := h_afford
  unfold discretionaryEnergy at h_cost
  linarith

/-! ## 6. Composition with the energy-Lyapunov certificate -/

/-- **Reserve protected from both sides.** In the sustainable regime (positive
    energy balance — the conclusion of `EnergyLyapunov.energy_lyapunov_certificate`),
    an affordable L3 draw leaves L1's survival reserve intact *while* that reserve
    is being replenished by positive energy flow. The energy-Lyapunov flow and the
    affordability gate jointly fence off `energyCriticalThreshold`. -/
theorem reserve_protected_both_sides (l1 : L1State) (cost : ℝ)
    (h_flow : 0 < EnergyLyapunov.energyBalance l1)
    (h_afford : canAffordPlan l1 cost) :
    l1.energy.val - cost ≥ energyCriticalThreshold
    ∧ 0 < EnergyLyapunov.energyBalance l1 :=
  ⟨afford_protects_reserve l1 cost h_afford, h_flow⟩

/-! ## 7. Persistence under L1 self-maintenance

L1's `maintainStability` updates only stress and stability — it never draws
energy. Combined with monotone stability, this makes the affordability and
reserve-safety gates *persistent*: once satisfied, L1's own self-maintenance can
never revoke them.

NOTE: this is persistence/invariance, NOT liveness. The modeled dynamics carry
no energy-stock or wall-state evolution (`maintainStability` leaves `energy`
fixed and does not touch `l2.wall`/`l3.blocked`), so the model cannot express
"L3 eventually becomes able to plan". Proving that would require adding energy
and wall dynamics to the transition system — deliberately out of scope here. -/

open EvoEcos.NoStrangeAttractor

/-- `maintainStability` leaves L1 energy untouched (it adjusts only stress/stability). -/
theorem maintainStability_preserves_energy (l1 : L1State) :
    (L1State.maintainStability l1).energy.val = l1.energy.val := rfl

/-- Discretionary energy is invariant under L1 self-maintenance. -/
theorem discretionaryEnergy_invariant (l1 : L1State) :
    discretionaryEnergy (L1State.maintainStability l1) = discretionaryEnergy l1 := by
  unfold discretionaryEnergy
  rw [maintainStability_preserves_energy]

/-- **Plan affordability persists** across one step of L1 self-maintenance. -/
theorem afford_persists (l1 : L1State) (cost : ℝ) (h : canAffordPlan l1 cost) :
    canAffordPlan (L1State.maintainStability l1) cost := by
  obtain ⟨h0, hc⟩ := h
  exact ⟨h0, by rw [discretionaryEnergy_invariant]; exact hc⟩

/-- **Plan affordability persists for all time** under iterated self-maintenance. -/
theorem afford_persists_iter (l1 : L1State) (cost : ℝ) (h : canAffordPlan l1 cost) :
    ∀ n, canAffordPlan (iterateMaintainStability n l1) cost := by
  intro n
  induction n with
  | zero => simpa [iterateMaintainStability] using h
  | succ n ih =>
    simp only [iterateMaintainStability]
    exact afford_persists _ cost ih

/-- **Experiment affordability persists**: discretionary energy is invariant and
    stability is non-decreasing, so the stricter experiment gate stays satisfied. -/
theorem experiment_afford_persists (l1 : L1State) (cost : ℝ)
    (h : canAffordExperiment l1 cost) :
    canAffordExperiment (L1State.maintainStability l1) cost := by
  obtain ⟨h0, hc, hs⟩ := h
  refine ⟨h0, ?_, ?_⟩
  · rw [discretionaryEnergy_invariant]; exact hc
  · have hmono := stability_non_decreasing_maintain l1
    linarith

/-- Experiment affordability persists for all time under iterated self-maintenance. -/
theorem experiment_afford_persists_iter (l1 : L1State) (cost : ℝ)
    (h : canAffordExperiment l1 cost) :
    ∀ n, canAffordExperiment (iterateMaintainStability n l1) cost := by
  intro n
  induction n with
  | zero => simpa [iterateMaintainStability] using h
  | succ n ih =>
    simp only [iterateMaintainStability]
    exact experiment_afford_persists _ cost ih

/-- **Reserve protection persists for all time.** If L3 can afford an experiment,
    then at every future step of L1 self-maintenance the experiment's cost still
    leaves L1's survival reserve intact — the energy safety margin is never eroded
    by L1's own dynamics. -/
theorem reserve_protection_persists (l1 : L1State) (cost : ℝ)
    (h : canAffordExperiment l1 cost) :
    ∀ n, (iterateMaintainStability n l1).energy.val - cost ≥ energyCriticalThreshold := by
  intro n
  obtain ⟨_, hc, _⟩ := experiment_afford_persists_iter l1 cost h n
  unfold discretionaryEnergy at hc
  linarith

end EvoEcos.L3Affordability
