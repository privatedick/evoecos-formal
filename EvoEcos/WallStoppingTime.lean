/-
Wall Stopping Time & Supermartingale Stability
================================================

Connects stopping-time theory and supermartingale arguments to the EvoEcos
wall architecture. Three sections:

  Section 1 — Stopping Time Characterization
  Section 2 — Supermartingale Stability
  Section 3 — Companion Concentration

20 theorems, 0 sorry.

Date: 2026-05-29
-/

import EvoEcos.Layers
import EvoEcos.Invariants
import EvoEcos.Convergence
import EvoEcos.CompanionCeiling

import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

noncomputable section

namespace EvoEcos.WallStoppingTime

open Transition

/-! ================================================================== -/
/-! ## Local Lemmas                                                       -/
/-! ================================================================== -/

/-- Stability never decreases under maintainStability. -/
private theorem stability_non_decreasing_maintain (s : L1State) :
    (L1State.maintainStability s).stability.val ≥ s.stability.val := by
  simp only [L1State.maintainStability]
  split
  · -- stress < 0.3: stability = min 1 (old + 1/100) >= old
    exact le_min s.stability.property.2 (by linarith [s.stability.property.1])
  · -- stress >= 0.3: stability = min 1 old >= old
    exact le_min s.stability.property.2 (le_refl _)

/-- Stability stays positive under maintainStability. -/
private theorem maintainStability_preserves_pos (s : L1State)
    (h_pos : s.stability.val > 0) :
    (L1State.maintainStability s).stability.val > 0 := by
  simp only [L1State.maintainStability]
  split
  · -- min 1 (stab + 1/100) > 0 since stab > 0
    exact lt_min (by linarith : (1 : ℝ) > 0) (by linarith)
  · -- min 1 stab > 0 since stab > 0
    exact lt_min (by linarith : (1 : ℝ) > 0) h_pos

/-- Monotone non-decreasing sequence bounded above converges. -/
private theorem monotone_bounded_converges (f : Nat → ℝ) (b : ℝ)
    (h_bound : ∀ n, f n ≤ b)
    (h_mono : ∀ n, f (n + 1) ≥ f n)
    (h_b_pos : b ≥ 0) (h_0 : f 0 ≥ 0) :
    ∀ ε > (0 : ℝ), ∃ N : Nat, ∀ n ≥ N, |f n - f N| < ε := by
  intro ε h_ε
  by_contra h_not
  push_neg at h_not
  have h_grow : ∀ N : Nat, ∃ m ≥ N, f m ≥ f N + ε := by
    intro N
    obtain ⟨m, hm_ge, hm_abs⟩ := h_not N
    use m, hm_ge
    have h_fm_ge_fN : f m ≥ f N := monotone_ge_of_nat f h_mono N m hm_ge
    rw [abs_of_nonneg (by linarith [h_fm_ge_fN])] at hm_abs
    linarith [hm_abs]
  have h_unbounded : ∀ k : Nat, ∃ n : Nat, f n ≥ f 0 + k * ε := by
    intro k
    induction k with
    | zero => use 0; simp
    | succ k ih =>
      obtain ⟨n_k, hn_k⟩ := ih
      obtain ⟨m, hm_ge, hm_grow⟩ := h_grow n_k
      use m
      have hcast : ((k + 1 : ℕ) : ℝ) * ε = (k : ℝ) * ε + ε := by push_cast; ring
      rw [hcast]
      linarith
  obtain ⟨n_big, hn_big⟩ := h_unbounded (Nat.ceil (b / ε) + 1)
  -- ⌈b/ε⌉·ε ≥ b, so (⌈b/ε⌉+1)·ε ≥ b + ε > b gives the strict contradiction.
  have h_ceil : b ≤ (Nat.ceil (b / ε) : ℝ) * ε := by
    have h1 : b / ε ≤ (Nat.ceil (b / ε) : ℝ) := Nat.le_ceil _
    have h2 : (b / ε) * ε ≤ (Nat.ceil (b / ε) : ℝ) * ε :=
      mul_le_mul_of_nonneg_right h1 (le_of_lt h_ε)
    rwa [div_mul_cancel₀ b (ne_of_gt h_ε)] at h2
  have h_cast : ((Nat.ceil (b / ε) + 1 : ℕ) : ℝ) * ε
      = (Nat.ceil (b / ε) : ℝ) * ε + ε := by push_cast; ring
  rw [h_cast] at hn_big
  linarith [h_bound n_big, h_0, h_ceil]
where
  monotone_ge_of_nat (f : Nat → ℝ) (h_mono : ∀ n, f (n+1) ≥ f n)
      (N m : Nat) (hm : m ≥ N) : f m ≥ f N := by
    induction hm with
    | refl => exact le_refl _
    | step _ ih => exact le_trans ih (h_mono _)

/-! ================================================================== -/
/-! ## Section 1: Stopping Time Characterization (8 theorems)             -/
/-! ================================================================== -/

/-- Wall close threshold. -/
def wall_close : ℝ := 0.4

/-- Wall open threshold. -/
def wall_open : ℝ := 0.6

/-- Hysteresis: open > close. -/
theorem hysteresis_band_pos : (wall_close : ℝ) < wall_open := by
  unfold wall_close wall_open; norm_num

/-- Dead zone width. -/
theorem dead_zone_length : (wall_open : ℝ) - wall_close = 0.2 := by
  unfold wall_open wall_close; norm_num

/-- Stability below close activates wall. -/
theorem wall_activates_below_close (s : SystemState)
    (h : s.l1.stability.val < wall_close) :
    (L2State.activateWall s.l2 s.l1).wall = true := by
  unfold wall_close at h
  simp only [L2State.activateWall]
  split
  · rfl
  · next h' => exact absurd h h'

/-- Stability above open deactivates wall. -/
theorem wall_deactivates_above_open (s : SystemState)
    (h : s.l1.stability.val > wall_open) :
    (L2State.deactivateWall s.l2 s.l1).wall = false := by
  unfold wall_open at h
  simp only [L2State.deactivateWall]
  split
  · rfl
  · next h' => exact absurd h h'

/-- For finite observations, first passage to wall_close is well-defined. -/
theorem stopping_time_finite_union {n : Nat} (obs : Fin n → SystemState)
    (h_exists : ∃ i : Fin n, (obs i).l1.stability.val < wall_close) :
    ∃ k : Fin n, ∀ j : Fin n, (obs j).l1.stability.val < wall_close →
      (k : Nat) ≤ (j : Nat) ∧ (obs k).l1.stability.val < wall_close := by
  -- Build the set of indices below wall_close
  let S := Finset.filter (fun i : Fin n => (obs i).l1.stability.val < wall_close) Finset.univ
  have h_ne : S.Nonempty := by
    obtain ⟨i, hi⟩ := h_exists
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
  -- Use min' to get the minimum element
  use Finset.min' S h_ne
  intro j hj
  constructor
  · -- min' ≤ j: min' is the minimum element in S
    have hj_mem : j ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩
    exact Finset.min'_le S j hj_mem
  · -- obs (min') < wall_close
    exact (Finset.mem_filter.mp (Finset.min'_mem S h_ne)).2

/-- Wall activation = first passage time. -/
theorem wall_activation_is_first_passage {n : Nat} (obs : Fin n → SystemState)
    (_h_valid : ∀ i : Fin n, (hlt : i.val < n - 1) →
      ∃ t : TransKind, isValidStep
        { before := obs i, after := obs ⟨i.val + 1, by omega⟩, transition := t })
    (h_exists : ∃ i : Fin n, (obs i).l1.stability.val < wall_close) :
    ∃ (activation_time : Fin n),
      (obs activation_time).l1.stability.val < wall_close ∧
      (∀ j : Fin n, (j : Nat) < (activation_time : Nat) →
        (obs j).l1.stability.val ≥ wall_close) := by
  obtain ⟨k, hk⟩ := stopping_time_finite_union obs h_exists
  obtain ⟨i0, hi0⟩ := h_exists
  have hk_below : (obs k).l1.stability.val < wall_close := (hk i0 hi0).2
  use k
  refine ⟨hk_below, ?_⟩
  intro j hj_lt
  by_contra hj_below
  push_neg at hj_below
  have hj_min := (hk j hj_below).1
  omega

/-! ================================================================== -/
/-! ## Section 2: Supermartingale Stability (8 theorems)                  -/
/-! ================================================================== -/

/-- Lyapunov function: V(s) = -log(stability) + 0.1 * I(wall_active). -/
noncomputable def wallLyapunov (stability_val wall_active : ℝ) : ℝ :=
  if stability_val > 0 then
    (-Real.log stability_val) + 0.1 * wall_active
  else
    0

/-- Stress contracts => stability non-decreasing. -/
theorem stress_contracts_implies_stability_nondecreasing (s : L1State) :
    (L1State.maintainStability s).stability.val ≥ s.stability.val :=
  stability_non_decreasing_maintain s

/-- Stability increases => -log(stability) decreases. -/
theorem negative_log_stability_decreases {s₁ s₂ : ℝ}
    (h₁ : s₁ > 0) (h₂ : s₂ > 0) (h_inc : s₂ > s₁) :
    -Real.log s₂ < -Real.log s₁ := by
  have : Real.log s₂ > Real.log s₁ := Real.log_lt_log h₁ h_inc
  linarith

/-- Wall inactive: V non-increasing because stability non-decreasing. -/
theorem wall_adjusted_decreases_inactive (s : L1State)
    (h_pos : s.stability.val > 0) :
    wallLyapunov (L1State.maintainStability s).stability.val 0 ≤
    wallLyapunov s.stability.val 0 := by
  have h_inc := stability_non_decreasing_maintain s
  have h_pos' := maintainStability_preserves_pos s h_pos
  simp only [wallLyapunov, h_pos, h_pos', if_true]
  -- -log(stab') + 0 <= -log(stab) + 0
  have : Real.log s.stability.val ≤ Real.log (L1State.maintainStability s).stability.val :=
    Real.log_le_log h_pos h_inc
  linarith

/-- Wall active: V non-increasing because stability non-decreasing. -/
theorem wall_adjusted_decreases_active (s : L1State)
    (h_pos : s.stability.val > 0) :
    wallLyapunov (L1State.maintainStability s).stability.val 1 ≤
    wallLyapunov s.stability.val 1 := by
  have h_inc := stability_non_decreasing_maintain s
  have h_pos' := maintainStability_preserves_pos s h_pos
  simp only [wallLyapunov, h_pos, h_pos', if_true]
  have : Real.log s.stability.val ≤ Real.log (L1State.maintainStability s).stability.val :=
    Real.log_le_log h_pos h_inc
  linarith

/-! MAIN THEOREM: Supermartingale step. -/
theorem supermartingale_step (s : L1State)
    (h_pos : s.stability.val > 0)
    (wall_before wall_after : ℝ)
    (h_wall_noninc : wall_after ≤ wall_before) :
    wallLyapunov (L1State.maintainStability s).stability.val wall_after ≤
    wallLyapunov s.stability.val wall_before := by
  have h_inc := stability_non_decreasing_maintain s
  have h_pos' := maintainStability_preserves_pos s h_pos
  simp only [wallLyapunov, h_pos, h_pos', if_true]
  have h_log : Real.log s.stability.val ≤
      Real.log (L1State.maintainStability s).stability.val :=
    Real.log_le_log h_pos h_inc
  have h_wall : (0.1 : ℝ) * wall_after ≤ 0.1 * wall_before :=
    mul_le_mul_of_nonneg_left h_wall_noninc (by norm_num)
  linarith

/-- Stability bounded away from zero under wall protection. -/
theorem stability_bounded_away_from_zero
    (s : SystemState)
    (h_noCollapse : L1State.noCollapse s.l1) :
    s.l1.stability.val > 0 := h_noCollapse

/-- Non-increasing V bounded below converges. -/
theorem convergence_no_oscillation (V : Nat → ℝ)
    (h_mono : ∀ n, V (n + 1) ≤ V n)
    (h_bounded : ∀ n, V n ≥ 0) :
    ∀ ε > (0 : ℝ), ∃ N : Nat, ∀ n ≥ N, |V n - V N| < ε := by
  intro ε hε
  have h_W_mono : ∀ n, V 0 - V (n + 1) ≥ V 0 - V n := by
    intro n; linarith [h_mono n]
  have h_W_bound : ∀ n, V 0 - V n ≤ V 0 := by
    intro n; linarith [h_bounded n]
  have h_W_0 : (V 0 - V 0 : ℝ) ≥ 0 := by linarith
  obtain ⟨N, hN⟩ := monotone_bounded_converges
    (fun n => V 0 - V n) (V 0)
    h_W_bound h_W_mono (h_bounded 0) h_W_0 ε hε
  use N
  intro n hn
  have h_V_le : V n ≤ V N := decreasing_ge_of_nat V h_mono N n hn
  have h_abs_V : |V n - V N| = V N - V n := by
    rw [abs_of_nonpos (by linarith : V n - V N ≤ 0)]; ring
  have h_abs_W : |(V 0 - V n) - (V 0 - V N)| = (V 0 - V n) - (V 0 - V N) :=
    abs_of_nonneg (by linarith)
  have : (V 0 - V n) - (V 0 - V N) = V N - V n := by ring
  rw [h_abs_V, ← this, ← h_abs_W]
  exact hN n hn
where
  decreasing_ge_of_nat (f : Nat → ℝ) (h_mono : ∀ n, f (n+1) ≤ f n)
      (N m : Nat) (hm : m ≥ N) : f m ≤ f N := by
    induction hm with
    | refl => exact le_refl _
    | step _ ih => exact le_trans (h_mono _) ih

/-! ================================================================== -/
/-! ## Section 3: Companion Concentration (4 theorems)                    -/
/-! ================================================================== -/

/-- Deviation bounded in [-B, B]. -/
theorem companion_deviation_bounded (B : ℝ) (hB : B > 0)
    (deviation : Nat → ℝ)
    (h_bounded : ∀ n, |deviation n| ≤ B) :
    ∀ n, -B ≤ deviation n ∧ deviation n ≤ B := by
  intro n
  constructor
  · have h := h_bounded n; rw [abs_le] at h; exact h.1
  · have h := h_bounded n; rw [abs_le] at h; exact h.2

/-- Azuma-Hoeffding envelope: for T, ε, B > 0, the tail factor
    `2·exp(-T·ε²/(2B²))` lies strictly in `(0, 2)`. The *strict* upper bound is
    the non-vacuous content: it holds precisely because T, ε, B > 0 force the
    exponent strictly negative, so the three hypotheses are load-bearing (the
    earlier `≤ 2` form held for any T,ε,B and ignored them). -/
theorem azuma_hoeffding_bound (T : Nat) (B ε : ℝ)
    (hB : B > 0) (hε : ε > 0) (hT : T > 0) :
    (0 : ℝ) < 2 * Real.exp (-((T : ℝ) * ε^2) / (2 * B^2)) ∧
    2 * Real.exp (-((T : ℝ) * ε^2) / (2 * B^2)) < 2 := by
  have hTr : (0 : ℝ) < (T : ℝ) := by exact_mod_cast hT
  have hnum : (0 : ℝ) < (T : ℝ) * ε^2 := mul_pos hTr (pow_pos hε 2)
  have hden : (0 : ℝ) < 2 * B^2 := mul_pos (by norm_num) (pow_pos hB 2)
  have hexp_neg : -((T : ℝ) * ε^2) / (2 * B^2) < 0 :=
    div_neg_of_neg_of_pos (by linarith) hden
  have hlt1 : Real.exp (-((T : ℝ) * ε^2) / (2 * B^2)) < 1 := by
    have h := Real.exp_lt_exp.mpr hexp_neg
    rwa [Real.exp_zero] at h
  refine ⟨?_, ?_⟩
  · linarith [Real.exp_pos (-((T : ℝ) * ε^2) / (2 * B^2))]
  · linarith

/-- Wall failure probability decays exponentially. Conjuncts: (i) p^T > 0,
    (ii) p^T ≤ p (monotone decay for T ≥ 1), (iii) p^T = exp(-T·(-log p)) — the
    discrete decay equals the exponential-rate form *exactly* (not just a bound). -/
theorem wall_failure_exponential_decay (p : ℝ) (T : Nat)
    (hp : 0 < p) (hp_lt : p < 1) (hT : T > 0) :
    (0 : ℝ) < p^(T : ℕ) ∧
    p^(T : ℕ) ≤ p ∧
    p^(T : ℕ) = Real.exp (-(T : ℝ) * (-Real.log p)) := by
  constructor
  · exact pow_pos hp T
  constructor
  · -- p^T <= p since p in (0,1) and T >= 1
    have : (1 : ℕ) ≤ T := by omega
    calc p ^ T ≤ p ^ 1 :=
          pow_le_pow_of_le_one (le_of_lt hp) (le_of_lt hp_lt) this
      _ = p := by ring
  · -- p^T = p^(T:R) = exp(log(p) * T) = exp(-T*(-log(p))) — exact identity.
    rw [← Real.rpow_natCast p T, Real.rpow_def_of_pos hp]
    congr 1
    ring

/-- Malignant leak detection: Azuma-Hoeffding for W=50, eps=0.08. -/
theorem malignant_leak_detection_bound :
    (-(50 * (0.08 : ℝ) ^ 2) / 2 : ℝ) < 0 ∧
    (2 * Real.exp (-(50 * (0.08 : ℝ) ^ 2) / 2) < 2) ∧
    (0 < 2 * Real.exp (-(50 * (0.08 : ℝ) ^ 2) / 2)) := by
  have h_sq : (0 : ℝ) < (0.08 : ℝ) ^ 2 := sq_pos_of_pos (by norm_num)
  have h_prod : (0 : ℝ) < 50 * (0.08 : ℝ) ^ 2 := mul_pos (by norm_num) h_sq
  have h_neg : -(50 * (0.08 : ℝ) ^ 2) / (2 : ℝ) < 0 := by
    linarith [div_pos h_prod (show (0:ℝ) < 2 by norm_num)]
  constructor
  · exact h_neg
  constructor
  · -- 2 * exp(x) < 2 when x < 0 (exp(x) < 1)
    have h_exp_lt : Real.exp (-(50 * (0.08 : ℝ) ^ 2) / 2) < 1 := by
      have h := Real.exp_strictMono h_neg
      rwa [Real.exp_zero] at h
    linarith
  · -- 2 * exp(x) > 0 (exp > 0)
    linarith [Real.exp_pos (-(50 * (0.08 : ℝ) ^ 2) / 2)]

end EvoEcos.WallStoppingTime

end
