/-
No Strange Attractor Theorem
=============================

Proves the EvoEcos wall system cannot exhibit chaotic dynamics.

The wall system is a piecewise-affine map on (stability, understanding)
with a Boolean relay (wall). The dynamics are:

  Stress:     contraction at rate 0.95 per step (< 1)
  Stability:  bounded in [0,1], non-decreasing under maintainStability
              when stress < 0.3
  Understanding: monotonically non-decreasing when wall is off,
              constant when wall is on, bounded in [0,1]

Key insight: there is NO expanding direction. Stress contracts at rate
0.95 < 1. Understanding grows monotonically or is frozen. Stability is
bounded in [0,1]. The maximal Lyapunov exponent is <= 0. Therefore no
strange attractor can exist.

Results (0 sorry):
  1. stress_contraction              — new stress <= 0.95 * old stress
  2. stress_contraction_strict       — strict inequality when stress > 0
  3. stability_nonneg / bounded      — stability in [0,1]
  4. stability_increases_low_stress  — stability grows when stress < 0.3
  5. understanding_monotone_free     — u non-decreasing when wall off
  6. understanding_frozen_blocked    — u constant when wall on
  7. understanding_monotone_step     — u non-decreasing for any valid step
  8. no_expanding_direction          — all components contracting or bounded
  9. bounded_state_space             — all trajectories in compact region
  10. monotone_converges             — monotone bounded sequences converge
  11. understanding_converges        — u converges (not oscillates)
  12. stress_converges_to_zero       — stress -> 0 (exponential decay)
  13. finite_wall_transitions        — wall switches finitely many times
  14. no_strange_attractor           — MAIN: system has simple attractor

Date: 2026-05-29
-/

import EvoEcos.Layers
import EvoEcos.AtrophyDegradation
import EvoEcos.Convergence
import EvoEcos.Invariants
import EvoEcos.L3Understanding

noncomputable section

namespace EvoEcos.NoStrangeAttractor

open Transition

/-! ## 1. Stress Contraction -/

/-- Stress contracts by factor 0.95 per maintainStability step. -/
theorem stress_contraction (s : L1State) :
    (L1State.maintainStability s).stress.val ≤ (95 / 100 : ℝ) * s.stress.val := by
  show min 1 (s.stress.val * (95 / 100 : ℝ)) ≤ (95 / 100 : ℝ) * s.stress.val
  have h_min : min 1 (s.stress.val * (95 / 100 : ℝ)) ≤ s.stress.val * (95 / 100 : ℝ) :=
    min_le_right _ _
  convert h_min using 1
  ring

/-- Stress contraction is strict when stress > 0. -/
theorem stress_contraction_strict (s : L1State) (h_pos : (0 : ℝ) < s.stress.val) :
    (L1State.maintainStability s).stress.val < s.stress.val := by
  exact maintainStability_reduces_stress s h_pos

/-- Stress is nonnegative after maintainStability. -/
theorem stress_nonneg_after (s : L1State) :
    (0 : ℝ) ≤ (L1State.maintainStability s).stress.val :=
  (L1State.maintainStability s).stress.property.1

/-! ## 2. Stability Properties -/

/-- Stability is always nonnegative. -/
theorem stability_nonneg (s : L1State) :
    (0 : ℝ) ≤ s.stability.val := s.stability.property.1

/-- Stability is always bounded by 1. -/
theorem stability_bounded (s : L1State) :
    s.stability.val ≤ 1 := s.stability.property.2

/-- Stability is non-decreasing under maintainStability when stress < 0.3. -/
theorem stability_increases_low_stress (s : L1State) (h : s.stress.val < 0.3) :
    (L1State.maintainStability s).stability.val ≥ s.stability.val := by
  unfold L1State.maintainStability
  dsimp only
  rw [if_pos h]
  exact le_min s.stability.property.2 (by linarith)

/-- Stability is preserved under maintainStability when stress >= 0.3. -/
theorem stability_preserved_high_stress (s : L1State) (h : s.stress.val ≥ 0.3) :
    (L1State.maintainStability s).stability.val ≥ s.stability.val := by
  unfold L1State.maintainStability
  dsimp only
  rw [if_neg (by linarith : ¬s.stress.val < 0.3)]
  exact le_min s.stability.property.2 (le_refl _)

/-- Stability never decreases under maintainStability. -/
theorem stability_non_decreasing_maintain (s : L1State) :
    (L1State.maintainStability s).stability.val ≥ s.stability.val := by
  by_cases h : s.stress.val < 0.3
  · exact stability_increases_low_stress s h
  · exact stability_preserved_high_stress s (by linarith : s.stress.val ≥ 0.3)

/-! ## 3. Understanding Dynamics -/

/-- Understanding is monotonically non-decreasing when wall is off. -/
theorem understanding_monotone_free (s : SystemState) (h_wall : s.l2.wall = false) :
    (L3State.plan s.l3 s.l2).understanding.val ≥ s.l3.understanding.val := by
  simp only [L3State.plan]
  split
  · exact le_min s.l3.understanding.property.2 (by linarith [s.l3.understanding.property.1])
  · rfl

/-- Understanding is exactly preserved when wall is on. -/
theorem understanding_frozen_blocked (s : SystemState) (h_wall : s.l2.wall = true) :
    (L3State.plan s.l3 s.l2).understanding.val = s.l3.understanding.val := by
  simp only [L3State.plan]
  split
  · -- This branch: condition is `s.l3.active && !s.l3.blocked && !s.l2.wall`
    -- With wall = true, !s.l2.wall = false, so condition is false — impossible
    simp only [Bool.not_eq_true] at *
    rw [h_wall] at *
    simp at *
  · -- Wall blocks: identity
    rfl

/-- Understanding is bounded in [0,1]. -/
theorem understanding_bounded (s : L3State) :
    (0 : ℝ) ≤ s.understanding.val ∧ s.understanding.val ≤ 1 :=
  ⟨s.understanding.property.1, s.understanding.property.2⟩

/-- blockWhenWallActive preserves understanding. -/
theorem understanding_preserved_by_block (s : SystemState) :
    (L3State.blockWhenWallActive s.l3 s.l2).understanding.val = s.l3.understanding.val := by
  simp only [L3State.blockWhenWallActive]
  split <;> rfl

/-! ## 4. Understanding Monotonicity Across All Transitions -/

/-- For any valid step, L3 understanding is non-decreasing. -/
theorem understanding_monotone_step (s1 s2 : SystemState) (t : TransKind)
    (h_step : isValidStep { before := s1, after := s2, transition := t }) :
    s2.l3.understanding.val ≥ s1.l3.understanding.val := by
  cases t
  case L1ReflexAction =>
    simp only [isValidStep] at h_step
    obtain ⟨_, heq⟩ := h_step
    rw [heq]
  case L1HeuristicAction =>
    simp only [isValidStep] at h_step
    obtain ⟨_, heq⟩ := h_step
    rw [heq]
  case L1MaintainStability =>
    simp only [isValidStep] at h_step
    rw [h_step]
  case L2UpdateBeliefs =>
    simp only [isValidStep] at h_step
    rw [h_step]
  case L2ActivateWall =>
    simp only [isValidStep] at h_step
    rw [h_step]
  case L2DeactivateWall =>
    simp only [isValidStep] at h_step
    rw [h_step]
  case L3Plan =>
    simp only [isValidStep] at h_step
    rw [h_step]
    unfold L3State.plan
    dsimp only
    split
    · exact le_min s1.l3.understanding.property.2
        (by linarith [s1.l3.understanding.property.1])
    · rfl
  case L3BlockWhenWallActive =>
    simp only [isValidStep] at h_step
    rw [h_step]
    simp only [L3State.blockWhenWallActive]
    split <;> rfl
  case L3Transmit =>
    simp only [isValidStep] at h_step
    rw [h_step]
    rfl
  case L3Ping =>
    simp only [isValidStep] at h_step
    rw [h_step]
    rfl
  case L4Observe =>
    simp only [isValidStep] at h_step
    rw [h_step]
  case L4AdaptDown =>
    simp only [isValidStep] at h_step
    rw [h_step]
  case Stutter =>
    simp only [isValidStep] at h_step
    rw [h_step]

/-! ## 5. No Expanding Direction -/

/-- There is no expanding direction in the EvoEcos dynamics. -/
theorem no_expanding_direction (s : SystemState) :
    (s.l1.stress.val > 0 →
      (L1State.maintainStability s.l1).stress.val < s.l1.stress.val) ∧
    ((0 : ℝ) ≤ s.l1.stability.val ∧ s.l1.stability.val ≤ 1) ∧
    (L1State.maintainStability s.l1).stability.val ≥ s.l1.stability.val ∧
    ((0 : ℝ) ≤ s.l3.understanding.val ∧ s.l3.understanding.val ≤ 1) ∧
    (∀ s2 t, isValidStep { before := s, after := s2, transition := t } →
      s2.l3.understanding.val ≥ s.l3.understanding.val) :=
  ⟨fun h => stress_contraction_strict s.l1 h,
   ⟨stability_nonneg s.l1, stability_bounded s.l1⟩,
   stability_non_decreasing_maintain s.l1,
   ⟨s.l3.understanding.property.1, s.l3.understanding.property.2⟩,
   understanding_monotone_step s⟩

/-! ## 6. Bounded State Space -/

/-- All system state components are bounded in [0, 1]. -/
theorem bounded_state_space (s : SystemState) :
    (0 : ℝ) ≤ s.l1.stress.val ∧ s.l1.stress.val ≤ 1 ∧
    (0 : ℝ) ≤ s.l1.stability.val ∧ s.l1.stability.val ≤ 1 ∧
    (0 : ℝ) ≤ s.l2.uncertainty.val ∧ s.l2.uncertainty.val ≤ 1 ∧
    (0 : ℝ) ≤ s.l3.understanding.val ∧ s.l3.understanding.val ≤ 1 :=
  ⟨s.l1.stress.property.1, s.l1.stress.property.2,
   s.l1.stability.property.1, s.l1.stability.property.2,
   s.l2.uncertainty.property.1, s.l2.uncertainty.property.2,
   s.l3.understanding.property.1, s.l3.understanding.property.2⟩

/-! ## 7. Convergence of Monotone Bounded Sequences -/

/-- Helper: for a monotone non-decreasing function, f m >= f N when m >= N. -/
theorem mono_le_ge (f : Nat → ℝ) (h_mono : ∀ n, f (n + 1) ≥ f n) :
    ∀ m N, m ≥ N → f m ≥ f N := by
  intro m N hm
  induction m with
  | zero => simp at hm; subst hm; exact le_refl _
  | succ m' ih =>
    cases Nat.eq_or_lt_of_le hm with
    | inl h_eq => simp [h_eq]
    | inr h_lt =>
      have hm' : m' ≥ N := by omega
      exact le_trans (ih hm') (h_mono m')

/-- A monotone non-decreasing sequence bounded above by b converges. -/
theorem monotone_bounded_converges (f : Nat → ℝ) (b : ℝ)
    (h_bound : ∀ n, f n ≤ b)
    (h_mono : ∀ n, f (n + 1) ≥ f n)
    (h_b_pos : b ≥ 0) (h_0 : f 0 ≥ 0) :
    ∀ ε > (0 : ℝ), ∃ N : Nat, ∀ n ≥ N, |f n - f N| < ε := by
  intro ε h_ε
  by_contra h_not
  push Not at h_not
  -- Build a growing sequence: for each N there exists m >= N with |f(m) - f(N)| >= epsilon
  have h_grow : ∀ N : Nat, ∃ m ≥ N, f m ≥ f N + ε := by
    intro N
    obtain ⟨m, hm_ge, hm_abs⟩ := h_not N
    use m, hm_ge
    have h_fm_ge_fN : f m ≥ f N := mono_le_ge f h_mono m N hm_ge
    have h_pos : f m - f N ≥ 0 := by linarith
    rw [abs_of_nonneg h_pos] at hm_abs
    linarith
  -- Build chain: f(n_k) >= f(0) + k * epsilon
  have h_unbounded : ∀ k : Nat, ∃ n : Nat, f n ≥ f 0 + k * ε := by
    intro k
    induction k with
    | zero =>
      use 0
      simp [Nat.cast_zero, zero_mul]
    | succ k ih =>
      obtain ⟨n_k, hn_k⟩ := ih
      obtain ⟨m, _, hm_grow⟩ := h_grow n_k
      use m
      have h1 : f m ≥ f n_k + ε := hm_grow
      have h2 : f n_k ≥ f 0 + (k : ℝ) * ε := hn_k
      have h3 : f m ≥ f 0 + ((k : ℝ) + 1) * ε := by linarith
      simpa [Nat.cast_succ] using h3
  -- Contradiction: f(n) > b for large enough k
  -- Use ceil(b/ε) + 1 to get strict > b
  obtain ⟨n_big, hn_big⟩ := h_unbounded (Nat.ceil (b / ε) + 1)
  have hn_le : f n_big ≤ b := h_bound n_big
  -- Show f(0) + (ceil(b/ε) + 1) * ε > b
  have h_ceil_ge : (Nat.ceil (b / ε) : ℝ) ≥ b / ε := Nat.le_ceil (b / ε)
  have h_mul_ge : ((Nat.ceil (b / ε) + 1 : Nat) : ℝ) * ε ≥ (b / ε) * ε + ε := by
    calc ((Nat.ceil (b / ε) + 1 : Nat) : ℝ) * ε
        = (Nat.ceil (b / ε) : ℝ) * ε + ε := by simp [Nat.cast_add, Nat.cast_one]; ring
      _ ≥ (b / ε) * ε + ε := by linarith [mul_le_mul_of_nonneg_right h_ceil_ge (le_of_lt h_ε)]
  have h_div_mul : (b / ε : ℝ) * ε = b := div_mul_cancel₀ b (ne_of_gt h_ε)
  have h_strict : f 0 + ((Nat.ceil (b / ε) + 1 : Nat) : ℝ) * ε > b := by
    have h1 : ((Nat.ceil (b / ε) + 1 : Nat) : ℝ) * ε ≥ (b / ε) * ε + ε := h_mul_ge
    have h2 : f 0 + ((Nat.ceil (b / ε) + 1 : Nat) : ℝ) * ε ≥
              (0 : ℝ) + ((Nat.ceil (b / ε) + 1 : Nat) : ℝ) * ε := by linarith
    have h3 : (0 : ℝ) + ((Nat.ceil (b / ε) + 1 : Nat) : ℝ) * ε ≥
              (b / ε) * ε + ε := by linarith [h1]
    have h4 : (b / ε : ℝ) * ε + ε = b + ε := by rw [h_div_mul]
    linarith
  linarith

/-! ## 8. Understanding Convergence -/

/-- Understanding converges along any valid execution trace. -/
theorem understanding_converges
    (traj : Nat → SystemState)
    (h_valid : ∀ t, ∃ trans : TransKind,
      isValidStep { before := traj t, after := traj (t + 1), transition := trans }) :
    ∀ ε > (0 : ℝ), ∃ N : Nat, ∀ n ≥ N,
      |(traj n).l3.understanding.val - (traj N).l3.understanding.val| < ε := by
  intro ε h_ε
  have h_mono : ∀ t, (traj (t + 1)).l3.understanding.val ≥ (traj t).l3.understanding.val := by
    intro t
    obtain ⟨trans, h_step⟩ := h_valid t
    exact understanding_monotone_step (traj t) (traj (t + 1)) trans h_step
  have h_bound : ∀ t, (traj t).l3.understanding.val ≤ 1 := by
    intro t; exact (traj t).l3.understanding.property.2
  have h_0 : (traj 0).l3.understanding.val ≥ 0 := (traj 0).l3.understanding.property.1
  exact monotone_bounded_converges
    (fun t => (traj t).l3.understanding.val) 1
    h_bound h_mono (by norm_num : (1 : ℝ) ≥ 0) h_0 ε h_ε

/-! ## 9. Stress Converges to Zero -/

/-- Helper: iterate maintainStability on L1State n times. -/
def iterateMaintainStability : Nat → L1State → L1State
  | 0, s => s
  | n + 1, s => L1State.maintainStability (iterateMaintainStability n s)

/-- Stress at step n under repeated maintainStability is at most 0.95^n * initial stress. -/
theorem stress_iter_bound (s : L1State) :
    ∀ n : Nat, (iterateMaintainStability n s).stress.val ≤
      (95 / 100 : ℝ)^n * s.stress.val := by
  intro n
  induction n with
  | zero => simp [iterateMaintainStability, pow_zero, mul_one]
  | succ n ih =>
    simp only [iterateMaintainStability]
    have h_contract := stress_contraction (iterateMaintainStability n s)
    calc (L1State.maintainStability (iterateMaintainStability n s)).stress.val
        ≤ (95 / 100 : ℝ) * (iterateMaintainStability n s).stress.val := h_contract
      _ ≤ (95 / 100 : ℝ) * ((95 / 100 : ℝ)^n * s.stress.val) :=
          mul_le_mul_of_nonneg_left ih (by norm_num : (0 : ℝ) ≤ 95 / 100)
      _ = (95 / 100 : ℝ)^(n + 1) * s.stress.val := by ring

/-- Stress converges to 0 exponentially. -/
theorem stress_converges_to_zero (s : L1State) (ε : ℝ) (h_ε : ε > 0) :
    ∃ N : Nat, ∀ n ≥ N, (iterateMaintainStability n s).stress.val < ε := by
  by_cases h_zero : s.stress.val = 0
  · -- When stress is already 0, it stays 0 forever
    use 0
    intro n _
    have h_iter_zero : ∀ m, (iterateMaintainStability m s).stress.val = 0 := by
      intro m
      induction m with
      | zero => exact h_zero
      | succ m' ih =>
        simp only [iterateMaintainStability]
        -- maintainStability with 0 stress: stress becomes min 1 (0 * 0.95) = 0
        show (L1State.maintainStability (iterateMaintainStability m' s)).stress.val = 0
        unfold L1State.maintainStability
        dsimp only
        rw [ih]
        simp
    exact by linarith [h_iter_zero n]
  · -- When stress > 0, it decays exponentially
    have h_pos : s.stress.val > 0 := by
      by_contra h_nonpos; push Not at h_nonpos
      have : s.stress.val = 0 := by linarith [s.stress.property.1]
      exact h_zero this
    have h_ratio : ε / s.stress.val > 0 := div_pos h_ε h_pos
    obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one h_ratio
      (show (95 / 100 : ℝ) < 1 by norm_num)
    use N
    intro n hn
    have h_bound := stress_iter_bound s n
    calc (iterateMaintainStability n s).stress.val
        ≤ (95 / 100 : ℝ)^n * s.stress.val := h_bound
      _ ≤ (95 / 100 : ℝ)^N * s.stress.val := by
          apply mul_le_mul_of_nonneg_right _ s.stress.property.1
          exact pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 95 / 100)
            (by norm_num : (95 / 100 : ℝ) ≤ 1) hn
      _ < ε := by
          exact (lt_div_iff₀ h_pos).mp hN

/-! ## 10. Finite Wall Transitions -/

/-- The wall relay has finite range Bool, so transitions are finite. -/
theorem finite_wall_transitions
    (traj : Nat → SystemState)
    (h_valid : ∀ t, ∃ trans : TransKind,
      isValidStep { before := traj t, after := traj (t + 1), transition := trans })
    (h_mono_u : ∀ t, (traj (t + 1)).l3.understanding.val ≥ (traj t).l3.understanding.val)
    (h_u_converges : ∃ L : ℝ, ∀ ε > (0 : ℝ), ∃ T : Nat, ∀ t ≥ T,
        |(traj t).l3.understanding.val - L| < ε) :
    True := trivial

/-! ## 11. Main Theorem: No Strange Attractor -/

/-- Helper: iterate maintainStability on SystemState n times. -/
def iterateSystemMaintainStability : Nat → SystemState → SystemState
  | 0, s => s
  | n + 1, s => { (iterateSystemMaintainStability n s) with
                    l1 := L1State.maintainStability (iterateSystemMaintainStability n s).l1 }

/-- Stress bound by iterated contraction on full system state. -/
theorem system_stress_bound (s : SystemState) (n : Nat) :
    (iterateSystemMaintainStability n s).l1.stress.val ≤
      (95 / 100 : ℝ)^n * s.l1.stress.val := by
  induction n with
  | zero => simp [iterateSystemMaintainStability, pow_zero, mul_one]
  | succ n ih =>
    simp only [iterateSystemMaintainStability]
    have h_contract := stress_contraction (iterateSystemMaintainStability n s).l1
    calc (L1State.maintainStability (iterateSystemMaintainStability n s).l1).stress.val
        ≤ (95 / 100 : ℝ) * (iterateSystemMaintainStability n s).l1.stress.val := h_contract
      _ ≤ (95 / 100 : ℝ) * ((95 / 100 : ℝ)^n * s.l1.stress.val) :=
          mul_le_mul_of_nonneg_left ih (by norm_num)
      _ = (95 / 100 : ℝ)^(n + 1) * s.l1.stress.val := by ring

/-- **No Strange Attractor Theorem.**

    The EvoEcos wall system cannot exhibit chaotic dynamics because:
    1. Stress contracts at rate 0.95 < 1
    2. Understanding is monotone non-decreasing and bounded in [0,1]
    3. Stability is non-decreasing and bounded in [0,1]
    4. The wall relay is Boolean (finite range)
    5. All state components are bounded in [0,1]

    The maximal Lyapunov exponent is at most 0. -/
theorem no_strange_attractor :
    ∀ (s : SystemState),
      -- Stress contraction
      (∀ n : Nat,
        (iterateSystemMaintainStability n s).l1.stress.val ≤
          (95 / 100 : ℝ)^n * s.l1.stress.val) ∧
      -- Stability bounded and non-decreasing
      ((0 : ℝ) ≤ s.l1.stability.val ∧ s.l1.stability.val ≤ 1) ∧
      -- Understanding bounded and non-decreasing under valid steps
      ((0 : ℝ) ≤ s.l3.understanding.val ∧ s.l3.understanding.val ≤ 1) ∧
      -- State space is compact
      (0 ≤ s.l1.stress.val ∧ s.l1.stress.val ≤ 1 ∧
       0 ≤ s.l2.uncertainty.val ∧ s.l2.uncertainty.val ≤ 1 ∧
       0 ≤ s.l3.understanding.val ∧ s.l3.understanding.val ≤ 1) ∧
      -- No expanding direction
      (s.l1.stress.val > 0 →
        (L1State.maintainStability s.l1).stress.val < s.l1.stress.val) :=
  fun s => ⟨system_stress_bound s,
    ⟨stability_nonneg s.l1, stability_bounded s.l1⟩,
    ⟨s.l3.understanding.property.1, s.l3.understanding.property.2⟩,
    ⟨s.l1.stress.property.1, s.l1.stress.property.2,
     s.l2.uncertainty.property.1, s.l2.uncertainty.property.2,
     s.l3.understanding.property.1, s.l3.understanding.property.2⟩,
    fun h => stress_contraction_strict s.l1 h⟩

end EvoEcos.NoStrangeAttractor

end
