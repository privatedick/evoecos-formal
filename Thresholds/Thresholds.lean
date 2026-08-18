/-
EvoEcos Thresholds Module
=========================

Formalization of critical thresholds and phase transitions
in the Stable Epistemic Bootstrap system.

Key Thresholds:
- L1 stability threshold (0.4) for L3 wall activation
- β* phase transition for information bottleneck
- I_exploit threshold for complexity activation
-/

import EvoEcos.Types
import InfoTheory.InfoTheory

noncomputable section

namespace EvoEcos.Thresholds

/-! ## Stability Thresholds -/

/-- L1 stability threshold for L3 wall activation -/
def L1_STABILITY_THRESHOLD : ℝ := 0.4

/-- L1 critical stability (below this = collapse risk) -/
def L1_CRITICAL_THRESHOLD : ℝ := 0.1

/-- L1 stress threshold for graceful degradation -/
def L1_STRESS_THRESHOLD : ℝ := 0.8

/-! ## Threshold Properties -/

/-- L1 threshold is in valid range -/
theorem l1_threshold_valid :
    0 < L1_STABILITY_THRESHOLD ∧ L1_STABILITY_THRESHOLD < 1 := by
  simp only [L1_STABILITY_THRESHOLD]
  norm_num

/-- Critical threshold is below stability threshold -/
theorem critical_below_stability :
    L1_CRITICAL_THRESHOLD < L1_STABILITY_THRESHOLD := by
  simp only [L1_CRITICAL_THRESHOLD, L1_STABILITY_THRESHOLD]
  norm_num

/-! ## Phase Transition Theory -/

/-- System phase based on L1 stability -/
inductive SystemPhase where
  | normal : SystemPhase      -- stability ≥ 0.4
  | stressed : SystemPhase    -- 0.1 ≤ stability < 0.4
  | critical : SystemPhase    -- stability < 0.1
deriving Repr, DecidableEq

/-- Determine system phase from stability -/
def classifyPhase (stability : Probability) : SystemPhase :=
  if stability.val < L1_CRITICAL_THRESHOLD then
    SystemPhase.critical
  else if stability.val < L1_STABILITY_THRESHOLD then
    SystemPhase.stressed
  else
    SystemPhase.normal

/-- Phase transition behavior -/
structure PhaseTransition where
  fromPhase : SystemPhase
  toPhase : SystemPhase
  trigger : String  -- What causes the transition
  response : String -- System response

/-! ## I_Exploit Threshold -/

/-- Threshold for activating L3 complexity -/
def I_EXPLOIT_THRESHOLD : ℝ := 0.1

/-- Check if I_exploit is above activation threshold -/
def shouldActivateComplexity (iExploit : ℝ) : Prop :=
  iExploit > I_EXPLOIT_THRESHOLD

/-- Type B environments should NOT activate complexity -/
theorem typeB_no_complexity (iExploit : ℝ) (h : iExploit < I_EXPLOIT_THRESHOLD) :
    ¬shouldActivateComplexity iExploit := by
  simp only [shouldActivateComplexity]
  nlinarith

/-! ## β* Phase Transitions by Environment Type -/

/-- β* values for different environment types -/
def betaStar (envType : String) : ℝ :=
  match envType with
  | "TypeA" => 0.368   -- Intermediate compression
  | "TypeB" => 0.211   -- Lower gain
  | "TypeC" => 1.000   -- Maximum compression
  | _ => 0.5

/-- β* ordering theorem -/
theorem beta_star_ordering :
    betaStar "TypeB" < betaStar "TypeA" ∧
    betaStar "TypeA" < betaStar "TypeC" := by
  simp only [betaStar]
  norm_num

/-- β* is always in valid range [0, 1] -/
theorem beta_star_in_range (envType : String) :
    0 ≤ betaStar envType ∧ betaStar envType ≤ 1 := by
  simp only [betaStar]
  split <;> norm_num

/-! ## Resource Thresholds -/

/-- Minimum energy for L3 activation -/
def L3_MIN_ENERGY : ℝ := 0.3

/-- Minimum computation for planning -/
def PLANNING_MIN_COMPUTATION : ℝ := 1.0

/-- Resource check for L3 activation -/
def canActivateL3 (energy computation : ℝ) : Prop :=
  energy ≥ L3_MIN_ENERGY ∧ computation ≥ PLANNING_MIN_COMPUTATION

/-! ## Graceful Degradation Thresholds -/

/-- Stress levels for degradation stages -/
inductive DegradationLevel where
  | none : DegradationLevel       -- stress < 0.3
  | mild : DegradationLevel       -- 0.3 ≤ stress < 0.6
  | moderate : DegradationLevel   -- 0.6 ≤ stress < 0.8
  | severe : DegradationLevel     -- stress ≥ 0.8
deriving Repr, DecidableEq

/-- Classify degradation level from stress -/
def classifyDegradation (stress : Probability) : DegradationLevel :=
  if stress.val ≥ 0.8 then DegradationLevel.severe
  else if stress.val ≥ 0.6 then DegradationLevel.moderate
  else if stress.val ≥ 0.3 then DegradationLevel.mild
  else DegradationLevel.none

/-- Severe degradation implies L3 blocked -/
theorem severe_implies_l3_blocked (stress : Probability)
    (h : classifyDegradation stress = DegradationLevel.severe) :
    stress.val ≥ 0.8 := by
  simp only [classifyDegradation] at h
  split at h
  · assumption
  · split at h
    · simp [*] at h
    · split at h <;> simp [*] at h

/-! ## Combined Threshold Invariants -/

/-- All thresholds are valid -/
theorem all_thresholds_valid :
    0 < L1_STABILITY_THRESHOLD ∧
    L1_CRITICAL_THRESHOLD < L1_STABILITY_THRESHOLD ∧
    0 < I_EXPLOIT_THRESHOLD ∧
    0 < L3_MIN_ENERGY := by
  simp only [L1_STABILITY_THRESHOLD, L1_CRITICAL_THRESHOLD,
             I_EXPLOIT_THRESHOLD, L3_MIN_ENERGY]
  norm_num

end EvoEcos.Thresholds

end
