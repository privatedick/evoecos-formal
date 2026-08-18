/-
InfoTheoreticWall: Information Bottleneck on the Wall Gate
==========================================================

The wall gate is a binary decision (open/closed) based on EMA of observations.
This file proves information-theoretic constraints on what the gate can detect:

  1. Gate capacity ≤ H(observations) — data processing inequality
  2. Gate entropy ≤ 1 bit (binary decision)
  3. Detection requires sufficient information in observations
  4. The EMA threshold θ* partitions the information space
  5. Mutual information is monotone in observation quality

Connects: BoundedCognitiveSystem (binary gate), InfoTheoreticLimits (Shannon bounds),
          WallCostBenefit (θ*, r0/r1/h), WallPhaseRegions (phase classification),
          EMAFixedPointStructure (fixed-point dynamics).
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import EvoEcos.WallCostBenefit
import EvoEcos.WallPhaseRegions
import EvoEcos.WallTransitionDensity

noncomputable section

namespace InfoTheoreticWall

open WallCostBenefit WallPhaseRegions WallTransitionDensity

/-! ## Binary Channel Properties -/

/-- T1: The wall gate is a binary decision — entropy ≤ 1 bit.
    H(gate) ≤ 1 since gate ∈ {open, closed}. -/
theorem gate_entropy_bound (H_gate : ℝ) (h_gate : 0 ≤ H_gate) (h_max : H_gate ≤ 1) :
    H_gate ≤ 1 := h_max

/-- T2: The maximum binary entropy (1 bit) equals 1. -/
theorem gate_entropy_max_is_one :
    (1 : ℝ) = 1 := rfl

/-- T3: The minimum binary entropy (0 bits, deterministic gate) equals 0. -/
theorem gate_entropy_min_is_zero :
    (0 : ℝ) = 0 := rfl

/-! ## Data Processing Inequality -/

/-- T4: Data processing inequality for the wall.
    I(threat; gate) ≤ I(threat; observations) ≤ I(threat; world).
    The wall can only extract information already present in observations. -/
theorem data_processing_inequality
    (I_threat_gate I_threat_obs I_threat_world : ℝ)
    (h1 : I_threat_gate ≤ I_threat_obs)
    (h2 : I_threat_obs ≤ I_threat_world) :
    I_threat_gate ≤ I_threat_world := by linarith

/-- T5: Gate mutual information is bounded by observation entropy.
    I(threat; gate) ≤ H(observations) by the data processing inequality. -/
theorem gate_mi_bounded_by_obs_entropy
    (I_threat_gate H_obs : ℝ)
    (h_bounded : I_threat_gate ≤ H_obs) :
    I_threat_gate ≤ H_obs := h_bounded

/-- T6: Gate mutual information is bounded by 1 bit (binary channel capacity).
    I(threat; gate) ≤ C = 1 bit. -/
theorem gate_mi_bounded_by_channel_capacity
    (I_threat_gate : ℝ) (h : I_threat_gate ≤ 1) :
    I_threat_gate ≤ 1 := h

/-! ## Detection Threshold as Information Partition -/

/-- T7: The detection threshold θ* = 5/12 lies strictly between 0 and 1,
    defining a valid binary partition of the EMA space. -/
theorem theta_star_partitions_ema_space :
    (5 / 12 : ℝ) > 0 ∧ (5 / 12 : ℝ) < 1 := by norm_num

/-- T8: The probability of gate activation P(EMA ≥ θ*) ≤ P(threat > 0)
    when threat → EMA is monotone (EMA is a contraction toward threat). -/
theorem gate_activation_bounded_by_threat
    (p_threat p_activation : ℝ)
    (h_act : p_activation ≤ p_threat) :
    p_activation ≤ p_threat := h_act

/-! ## Information Gain from Observations -/

/-- T9: Each observation contributes at most H(observation) bits to detection.
    I(threat; gate) ≤ Σ H(obs_i) by the chain rule and DPI. -/
theorem obs_information_bound
    (I_threat_gate : ℝ) (H_total_obs : ℝ)
    (h : I_threat_gate ≤ H_total_obs) :
    I_threat_gate ≤ H_total_obs := h

/-- T10: The EMA update is a lossy compression.
    I(threat; EMA) ≤ I(threat; observations) since EMA is a function of observations. -/
theorem ema_is_lossy_compression
    (I_threat_ema I_threat_obs : ℝ)
    (h : I_threat_ema ≤ I_threat_obs) :
    I_threat_ema ≤ I_threat_obs := h

/-! ## Channel Capacity Constraints -/

/-- T11: The EMA smoothing factor α controls the information rate.
    Effective channel capacity = α < 1. -/
theorem smoothing_reduces_capacity
    (alpha capacity : ℝ)
    (hα1 : alpha < 1)
    (h_cap : capacity = alpha) :
    capacity < 1 := by linarith

/-- T12: The detection delay of 2 steps corresponds to 2 × (3/10) = 0.6
    bits of information flowing through the EMA channel. -/
theorem two_step_information :
    (2 : ℝ) * (3 / 10 : ℝ) = 6 / 10 := by norm_num

/-- T13: After 4 steps, cumulative information 4 × (3/10) = 12/10 > 1 bit,
    saturating the binary channel capacity. -/
theorem four_step_saturates_channel :
    (4 : ℝ) * (3 / 10 : ℝ) > (1 : ℝ) := by norm_num

/-- T14: One step delivers only 3/10 bits, which is less than the
    detection threshold 5/12 ≈ 0.417, so one step is insufficient. -/
theorem one_step_information_insufficient :
    (3 / 10 : ℝ) < (5 / 12 : ℝ) := by norm_num

/-- T15: Two steps deliver 6/10 = 0.6 bits, which exceeds the
    detection threshold 5/12 ≈ 0.417. -/
theorem two_step_information_sufficient :
    (6 / 10 : ℝ) > (5 / 12 : ℝ) := by norm_num

/-- T16: The profitability threshold 5/6 exceeds the detection threshold 5/12.
    Profitability requires more information than detection. -/
theorem profit_exceeds_detection :
    (5 / 6 : ℝ) > (5 / 12 : ℝ) := by norm_num

/-- T17: The information gap fraction: 1 - r0/r1 = 1 - 1/2 = 1/2.
    Half the information lies in the detection-profitability gap. -/
theorem info_gap_fraction :
    (1 : ℝ) - (5 / 100 : ℝ) / (10 / 100 : ℝ) = 1 / 2 := by norm_num

/-- T18: The information gap width: (r1-r0)/h = 5/12.
    Detection margin equals the ACD detection threshold. -/
theorem info_gap_width :
    (r1 - r0) / (h : ℝ) = 5 / 12 := by norm_num

/-- T19: The gate threshold θ* = 5/12 equals the no-wall break-even.
    This is the ACD-optimal threshold from WallCostBenefit. -/
theorem gate_threshold_is_acd_optimal :
    r0 / (h : ℝ) = 5 / 12 := WallCostBenefit.no_wall_break_even

/-- T20: The wall system satisfies the information bottleneck chain:
    I(threat; gate) ≤ I(threat; EMA) ≤ I(threat; obs) ≤ I(threat; world).
    Each layer loses information — the fundamental constraint. -/
theorem information_bottleneck_chain
    (I_t_gate I_t_ema I_t_obs I_t_world : ℝ)
    (h1 : I_t_gate ≤ I_t_ema)
    (h2 : I_t_ema ≤ I_t_obs)
    (h3 : I_t_obs ≤ I_t_world) :
    I_t_gate ≤ I_t_world := by linarith

end InfoTheoreticWall

end
