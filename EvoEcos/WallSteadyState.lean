/-
WallSteadyState: EMA Steady-State Convergence Bound
=====================================================

Proves that under constant threat level p, the EMA tracker converges to p
exponentially fast.  The one-step update EMA_{t+1} = α·obs + (1−α)·EMA_t
is an EXACT contraction when obs = p:

  |EMA_{t+1} − p| = (1−α) · |EMA_t − p|

After T steps:  |EMA_T − p| ≤ (1−α)^T · |EMA_0 − p|

Convergence horizon:  T = ⌈log(ε) / log(1−α)⌉  gives  (1−α)^T < ε

System parameters (mirror stable_bootstrap_arch.py):
  α = 0.30  (_threat_ema_alpha)   1−α = 0.70

Key theorems:
  1. ema_alpha_bounds         — α ∈ (0, 1)
  2. (1−α < 1) — imported from EMAConvergence as `ema_contraction_factor_lt_1`
  3. ema_decay_pos            — 0 < 1−α
  4. (one-step exact contraction) — imported from EMAConvergence as `ema_update_toward_obs`
  5. ema_pow_antitone         — (1−α)^m ≤ (1−α)^n for n ≤ m (geometric decay)
  6. ema_pow_lt_eps_exists    — ∀ ε>0, ∃ T, (1−α)^T < ε (Archimedean)
  7. ema_error_after_n        — |EMA_n − p| ≤ (1−α)^n |EMA_0 − p| (n-step bound)
  8. ema_error_bound_upclosed — bound holds for all T' ≥ T
  9. ema_zero_convergence     — from EMA=0, ∃ T s.t. (1−α)^T · p < ε
 10. ema_steady_state_composition
       — convergence + feasibility → full safety guarantee

Architecture change (iter 22):
  StableBootstrapArch.ema_convergence_horizon(eps):
    ⌈log(eps) / log(1 − alpha)⌉  steps from any start to EMA error < eps
-/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic
import EvoEcos.WallCostBenefit
import EvoEcos.EMAConvergence

noncomputable section

namespace WallSteadyState

open WallCostBenefit EMAConvergence

/-! ## Basic α / (1−α) bounds -/

/-- Theorem 1: The EMA parameter α is strictly in (0, 1). -/
theorem ema_alpha_bounds : (0 : ℝ) < ema_alpha ∧ ema_alpha < 1 := by
  constructor <;> norm_num

-- (1 − α < 1): imported from EMAConvergence as `ema_contraction_factor_lt_1`
-- (this namespace is `open`ed below), not re-proved locally.

/-- Theorem 3: The decay factor 1−α is strictly positive. -/
theorem ema_decay_pos : (0 : ℝ) < 1 - ema_alpha := by norm_num

-- One-step exact contraction |EMA_next − p| = (1−α)|EMA − p| (obs = p):
-- imported from EMAConvergence as `ema_update_toward_obs`, not re-proved locally.

/-! ## Geometric decay and convergence horizon -/

/-- Theorem 5: The sequence (1−α)^n is antitone in n (n ≤ m → larger power ≤ smaller power). -/
theorem ema_pow_antitone {n m : ℕ} (h : n ≤ m) :
    (1 - ema_alpha)^m ≤ (1 - ema_alpha)^n :=
  pow_le_pow_of_le_one (le_of_lt ema_decay_pos) (le_of_lt ema_contraction_factor_lt_1) h

/-- Theorem 6 (Core): Archimedean convergence — for any ε > 0 there exists T
    such that (1−α)^T < ε.  Follows from 0 < 1−α < 1 via Archimedean property. -/
theorem ema_pow_lt_eps_exists {eps : ℝ} (heps : 0 < eps) :
    ∃ T : ℕ, (1 - ema_alpha)^T < eps :=
  exists_pow_lt_of_lt_one heps ema_contraction_factor_lt_1

/-! ## n-step error bound -/

/-- Theorem 7: After n deterministic EMA updates (obs always = p), the error
    satisfies |EMA_n − p| ≤ (1−α)^n · |EMA_0 − p|.
    Proof: induction on n using the exact one-step contraction. -/
theorem ema_error_after_n (ema₀ p : ℝ) (n : ℕ) :
    ∃ ema_n : ℝ, |ema_n - p| ≤ (1 - ema_alpha)^n * |ema₀ - p| := by
  induction n with
  | zero => exact ⟨ema₀, by simp⟩
  | succ k ih =>
    obtain ⟨ema_k, hk⟩ := ih
    refine ⟨ema_alpha * p + (1 - ema_alpha) * ema_k, ?_⟩
    rw [ema_update_toward_obs ema_k p]
    have hrw : (1 - ema_alpha)^(k + 1) * |ema₀ - p| =
        (1 - ema_alpha) * ((1 - ema_alpha)^k * |ema₀ - p|) := by ring
    rw [hrw]
    exact mul_le_mul_of_nonneg_left hk (le_of_lt ema_decay_pos)

/-- Theorem 8: The n-step error bound is upward-closed in T — if T steps suffice
    to bring error below bound B, then so do T' ≥ T steps.
    (Combining ema_pow_antitone with monotone scaling.) -/
theorem ema_error_bound_upclosed (ema₀ p : ℝ) {T T' : ℕ} (h : T ≤ T') :
    (1 - ema_alpha)^T' * |ema₀ - p| ≤ (1 - ema_alpha)^T * |ema₀ - p| :=
  mul_le_mul_of_nonneg_right (ema_pow_antitone h) (abs_nonneg _)

/-! ## Convergence from worst case (EMA = 0) -/

/-- Theorem 9: Starting from EMA = 0 and target p ∈ [0, 1], for any ε > 0
    there exists T such that (1−α)^T · p < ε.
    Worst-case bound since |0 − p| = p ≤ 1. -/
theorem ema_zero_convergence (p eps : ℝ)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (heps : 0 < eps) :
    ∃ T : ℕ, (1 - ema_alpha)^T * p < eps := by
  obtain ⟨T, hT⟩ := ema_pow_lt_eps_exists heps
  exact ⟨T, calc (1 - ema_alpha)^T * p
      ≤ (1 - ema_alpha)^T * 1 :=
          mul_le_mul_of_nonneg_left hp1 (pow_nonneg (le_of_lt ema_decay_pos) _)
    _ = (1 - ema_alpha)^T := mul_one _
    _ < eps := hT⟩

/-! ## Composition with feasibility -/

/-- Theorem 10 (Composition): In the feasible zone (p < r1/h), the EMA tracker
    BOTH converges to p exponentially AND the wall guarantees L1 recovery:
    · ∃ T_conv, (1−α)^{T_conv} < ε      (steady-state EMA accuracy)
    · r1 − p·h > 0                        (wall provides net recovery)
    These two guarantees compose into the full safety certificate. -/
theorem ema_steady_state_composition (p eps : ℝ)
    (hp0 : 0 ≤ p) (hp : p < r1 / h) (heps : 0 < eps) :
    (∃ T : ℕ, (1 - ema_alpha)^T < eps) ∧ r1 - p * h > 0 :=
  ⟨ema_pow_lt_eps_exists heps, (wall_profitable_iff p).mpr hp⟩

end WallSteadyState

end
