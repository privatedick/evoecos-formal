/-
Decision Cost: openness-weighted planning cost
===============================================

`L3Affordability.planCost` prices every plan as `depth × nSims × 0.1` — flat in
*what kind* of decision the plan resolves. Two plans of equal depth and
simulation count cost the same whether one answers a reflex ("dark mode?") and
the other an open-ended strategic question ("what is the deployment policy?").
That conflates routine and executive load: the runtime's affordability gate then
behaves as if every decision costs the same fraction of the discretionary budget,
which is blind to the empirical fact (Kool, Westbrook & Braver on effort
discounting; Shenhav et al. on the expected-value-of-control) that cognitive
cost scales with the *openness* of the decision — how under-determined the answer
is by habit.

This module makes decision-openness a first-class multiplier of `planCost`,
without re-proving the affordability machinery:

    decisionCost openness depth nSims := openness · planCost depth nSims

HONESTY BOUND: `openness` is a *modeling parameter*, the same epistemic status as
the hard-coded `1/10` in `planCost`. This module does NOT instantiate a calibrated
unit of cognitive effort — no measurement instrument, no fitted scale. It only
makes the dimension the flat model was blind to (decision-openness) first-class,
so the affordability theorem `afford_protects_reserve` extends to it. The
informal "Glootie" scale (0.1 reflex … 5 executive) is a mnemonic for the axis,
not a claim that this file measures it.

Non-breaking anchor: `decisionCost 1 depth nSims = planCost depth nSims`, i.e.
openness = 1 reproduces the existing flat model exactly. Lower openness discounts
(routine decisions consume less of the survival-proximate reserve); higher
openness surcharges (executive decisions consume more, hitting the affordability
ceiling in fewer decisions).

Composes (does not re-prove):
  - L3Affordability.planCost / planCost_nonneg   (the flat base cost)
  - L3Affordability.canAffordPlan                (the budget gate)
  - L3Affordability.afford_protects_reserve      (reserve-safety certificate)
  - L1EnergySufficiency.energyCriticalThreshold  (the protected reserve)

Downstream consumer: `_estimate_plan_cost` / `_can_afford_plan`
(stable_bootstrap_arch.py), once the openness multiplier is wired there with
default openness = 1.0 (preserving current behaviour).
-/

import EvoEcos.Layers
import EvoEcos.L1EnergySufficiency
import EvoEcos.L3Affordability
import Mathlib.Data.Real.Basic

noncomputable section

namespace EvoEcos.DecisionCost

open EvoEcos.L3Affordability

/-! ## 1. Openness-weighted decision cost (mirrors the Python runtime) -/

/-- Decision cost = openness × planCost. `openness` is a non-negative modeling
    multiplier on the *kind* of decision (0 = reflex / muscle-memory, 1 = the
    flat-baseline decision, > 1 = open-ended / executive). Composes with
    `L3Affordability.planCost`; does not redefine it. -/
def decisionCost (openness : ℝ) (depth nSims : Nat) : ℝ :=
  openness * planCost depth nSims

/-! ## 2. Cost-model lemmas -/

/-- Decision cost is non-negative whenever the openness weight is. -/
theorem decisionCost_nonneg (openness : ℝ) (depth nSims : Nat) (ho : 0 ≤ openness) :
    0 ≤ decisionCost openness depth nSims := by
  unfold decisionCost
  exact mul_nonneg ho (planCost_nonneg depth nSims)

/-- Decision cost is monotone in the openness weight: a more open-ended decision
    of the same plan shape costs at least as much. -/
theorem decisionCost_mono_openness (o₁ o₂ : ℝ) (depth nSims : Nat)
    (h : o₁ ≤ o₂) :
    decisionCost o₁ depth nSims ≤ decisionCost o₂ depth nSims := by
  unfold decisionCost
  exact mul_le_mul_of_nonneg_right h (planCost_nonneg depth nSims)

/-- A fully-closed (reflex) decision costs nothing on the openness axis — the
    formal content of "muscle memory ≈ 0". -/
theorem reflex_decision_zero (depth nSims : Nat) :
    decisionCost 0 depth nSims = 0 := by
  unfold decisionCost
  exact zero_mul _

/-! ## 3. Calibration anchors: the new model reduces to the flat one at openness 1 -/

/-- **Non-breaking anchor.** At openness = 1 the openness-weighted cost is
    *exactly* the flat `planCost`. Wiring this with default openness = 1.0 leaves
    every existing affordability gate numerically unchanged. -/
theorem decisionCost_eq_flat_at_unit (depth nSims : Nat) :
    decisionCost 1 depth nSims = planCost depth nSims := by
  unfold decisionCost
  exact one_mul _

/-- A decision of openness ≤ 1 costs no more than the flat baseline. -/
theorem decisionCost_le_flat (openness : ℝ) (depth nSims : Nat)
    (h : openness ≤ 1) :
    decisionCost openness depth nSims ≤ planCost depth nSims := by
  unfold decisionCost
  have h1 : openness * planCost depth nSims ≤ 1 * planCost depth nSims :=
    mul_le_mul_of_nonneg_right h (planCost_nonneg depth nSims)
  rwa [one_mul] at h1

/-- A decision of openness ≥ 1 costs no less than the flat baseline (executive
    load is a surcharge, never a discount relative to the calibrated base). -/
theorem flat_le_decisionCost (openness : ℝ) (depth nSims : Nat)
    (h : 1 ≤ openness) :
    planCost depth nSims ≤ decisionCost openness depth nSims := by
  unfold decisionCost
  have h1 : 1 * planCost depth nSims ≤ openness * planCost depth nSims :=
    mul_le_mul_of_nonneg_right h (planCost_nonneg depth nSims)
  rwa [one_mul] at h1

/-! ## 4. Affordability is antitone in openness (the central claim) -/

/-- **Affordability shrinks as openness grows.** If a plan is affordable at
    openness `o₂`, it is affordable at any lower openness `o₁ ≤ o₂`: a routine
    decision never exhausts a budget that an open-ended one would fit in. This is
    the static, dynamics-free form of "executive load hits the ceiling sooner" —
    no energy-stock evolution is invented (the L3Affordability model has none). -/
theorem affordability_antitone_openness (l1 : L1State) (o₁ o₂ : ℝ)
    (depth nSims : Nat) (h : o₁ ≤ o₂) (ho₁ : 0 ≤ o₁)
    (h_afford : canAffordPlan l1 (decisionCost o₂ depth nSims)) :
    canAffordPlan l1 (decisionCost o₁ depth nSims) := by
  obtain ⟨h0, hc⟩ := h_afford
  refine ⟨decisionCost_nonneg o₁ depth nSims ho₁, ?_⟩
  have hmono := decisionCost_mono_openness o₁ o₂ depth nSims h
  linarith

/-! ## 5. Reserve protection extends to the openness-weighted cost -/

/-- Executing any affordable openness-weighted plan still leaves L1's protected
    survival reserve intact — `afford_protects_reserve` applies unchanged, because
    the affordability gate quantifies over the cost. -/
theorem decisionCost_protects_reserve (l1 : L1State) (openness : ℝ)
    (depth nSims : Nat) (h : canAffordPlan l1 (decisionCost openness depth nSims)) :
    l1.energy.val - decisionCost openness depth nSims ≥ energyCriticalThreshold :=
  afford_protects_reserve l1 (decisionCost openness depth nSims) h

/-! ## 6. Capstone: an open decision is both affordable-by-lowering AND a surcharge -/

/-- If a fully-or-more-open (`o₂ ≥ 1`) decision is affordable, then (a) the cheaper
    routine variant `o₁` is affordable *and* protects the reserve, and (b) the
    open variant costs at least the flat baseline. A single affordability
    assumption discharges reserve-safety at lower openness and the surcharge bound
    at higher openness — the two directions in which the openness axis bends the
    flat model. -/
theorem open_decision_tighter_reserve (l1 : L1State) (o₁ o₂ : ℝ)
    (depth nSims : Nat) (h12 : o₁ ≤ o₂) (h2 : 1 ≤ o₂) (ho₁ : 0 ≤ o₁)
    (h_afford : canAffordPlan l1 (decisionCost o₂ depth nSims)) :
    (l1.energy.val - decisionCost o₁ depth nSims ≥ energyCriticalThreshold)
      ∧ planCost depth nSims ≤ decisionCost o₂ depth nSims := by
  refine ⟨?_, flat_le_decisionCost o₂ depth nSims h2⟩
  exact afford_protects_reserve l1 (decisionCost o₁ depth nSims)
    (affordability_antitone_openness l1 o₁ o₂ depth nSims h12 ho₁ h_afford)

end EvoEcos.DecisionCost
