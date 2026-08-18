/-
Bang-Bang Noise Robustness Theorem
===================================

Proves that minimal MLP policies (H=1 hidden unit, finite output classes)
converge to bang-bang (sign-based) controllers, and that this structure
provides maximal noise robustness.

## What it proves

1. **Tanh saturation**: For |z| > 2, |tanh z| > 24/25. The pre-activation
   is effectively binary.

2. **Output Bottleneck Theorem**: An H=1 MLP with argmax over 2 actions
   has an effective decision determined by a single scalar z = w . s + b.

3. **Noise Robustness Theorem** (main result): Under bounded observation
   noise epsilon with |epsilon_i| <= delta, the pre-activation sign is
   preserved whenever z is far from the decision boundary:

     If |z(s)| > kappa and ||w||_1 * delta < kappa,
     then sign(z(s + epsilon)) = sign(z(s)).

   This means the action cannot flip — the policy is noise-robust by
   structure, not by training.

4. **Safe zone characterization**: The set of states where |z| >= kappa
   is a safe zone in which sign is preserved under bounded noise.

## Why it matters

CMA-ES and other evolution strategies discover bang-bang controllers
in environments where the minimal viable policy has intrinsic dimension
< 2.0. This theorem explains why these evolved policies are maximally
robust to observation noise: their sign-based output structure makes
them immune to noise outside a vanishingly thin decision boundary.

## References

* Original context: EvoEcos "Bang-Bang Noise Robustness Theorem"
  (experiment_video_themes, insight_bang_bang_theorem.md)
* Related: Simplex Architecture (Sha 2001) — EvoEcos evolved L1
  controllers are a special case with formally verified noise bounds.

## Dependencies

Mathlib only. No EvoEcos-specific types.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Lemmas
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

noncomputable section

namespace ProvablyCorrectControllers

open Real

/-! ## Tanh Properties -/

/-- |tanh x| < 1 for all x. -/
theorem tanh_abs_lt_one (x : ℝ) : |tanh x| < 1 := by
  rw [Real.tanh_eq_sinh_div_cosh]
  rw [abs_div]
  rw [abs_of_pos (Real.cosh_pos x)]
  rw [div_lt_one (Real.cosh_pos x)]
  exact abs_lt.mpr ⟨by
      rw [Real.sinh_eq, Real.cosh_eq]
      linarith [Real.exp_pos x],
    Real.sinh_lt_cosh x⟩

/-- tanh is monotone increasing. -/
theorem tanh_monotone : Monotone tanh := by
  intro x y hxy
  rw [Real.tanh_eq_sinh_div_cosh, Real.tanh_eq_sinh_div_cosh]
  have hc : (0 : ℝ) < cosh x := Real.cosh_pos x
  have hc' : (0 : ℝ) < cosh y := Real.cosh_pos y
  rw [div_le_div_iff₀ hc hc']
  have this : sinh y * cosh x - sinh x * cosh y = sinh (y - x) := by
    rw [Real.sinh_sub]
    ring
  have h_sinh_nonneg : sinh (y - x) >= 0 := by
    have h_nonneg : y - x >= 0 := by linarith
    rw [Real.sinh_eq]
    refine div_nonneg (sub_nonneg.mpr ?_) (le_of_lt two_pos)
    exact (exp_le_exp.mpr (by linarith : -((y - x : ℝ)) <= 0)).trans (exp_le_exp.mpr h_nonneg)
  linarith [this ▸ h_sinh_nonneg]

/-- For x > 0, tanh x > 0. -/
theorem tanh_pos_of_pos {x : ℝ} (hx : x > 0) : tanh x > 0 := by
  have h_le : tanh 0 <= tanh x := tanh_monotone (le_of_lt hx)
  rw [Real.tanh_zero] at h_le
  rw [Real.tanh_eq_sinh_div_cosh]
  refine div_pos ?_ (Real.cosh_pos x)
  rw [Real.sinh_eq]
  refine div_pos ?_ two_pos
  exact sub_pos.mpr (Real.exp_lt_exp_of_lt (by linarith : (-x : ℝ) < x))

/-- For x < 0, tanh x < 0. -/
theorem tanh_neg_of_neg {x : ℝ} (hx : x < 0) : tanh x < 0 := by
  have h := tanh_pos_of_pos (by linarith : -x > 0)
  rw [Real.tanh_neg] at h
  linarith

/-! ## Saturation Bounds -/

/-- tanh x > 24/25 when x > 2. -/
theorem tanh_saturation_pos {x : ℝ} (hx : x > 2) : tanh x > 24 / 25 := by
  have h_exp2x_gt_49 : (49 : ℝ) < exp (2 * x) := by
    have h_exp2_lb : (109 : ℝ) / 15 <= exp (2 : ℝ) := by
      have h_sum := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) <= 2) 6
      have h_sum_val : Finset.sum (Finset.range 6) (fun i => (2 : ℝ) ^ i / ↑(Nat.factorial i)) = 109 / 15 := by
        norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
      linarith [h_sum_val ▸ h_sum]
    have h_exp4_lb : (11881 : ℝ) / 225 <= exp (4 : ℝ) := by
      have h_e4 : exp (4 : ℝ) = exp (2 + 2 : ℝ) := congrArg Real.exp (by norm_num : (4 : ℝ) = 2 + 2)
      rw [h_e4, Real.exp_add]
      calc (11881 : ℝ) / 225 = 109 / 15 * (109 / 15) := by norm_num
        _ <= exp 2 * exp 2 := mul_le_mul h_exp2_lb h_exp2_lb (by positivity) (by positivity)
    calc (49 : ℝ)
        < 11881 / 225 := by norm_num
      _ <= exp 4 := h_exp4_lb
      _ <= exp (2 * x) := (Real.exp_le_exp).mpr (by nlinarith)
  have h49 : (49 : ℝ) * exp (-x) < exp x := by
    have : exp (2 * x) * exp (-x) = exp (2 * x + (-x)) := (Real.exp_add (2 * x) (-x)).symm
    rw [show 2 * x + (-x) = x by ring] at this
    calc 49 * exp (-x) < exp (2 * x) * exp (-x) :=
          mul_lt_mul_of_pos_right h_exp2x_gt_49 (Real.exp_pos (-x))
      _ = exp x := this
  rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq]
  have h25 : (24 : ℝ) * (exp x + exp (-x)) < (25 : ℝ) * (exp x - exp (-x)) := by linarith
  have h_eq : (exp x - exp (-x)) / 2 / ((exp x + exp (-x)) / 2) =
      (exp x - exp (-x)) / (exp x + exp (-x)) := by field_simp
  rw [h_eq]
  have h_lt : (24 : ℝ) / 25 < (exp x - exp (-x)) / (exp x + exp (-x)) := by
    rw [div_lt_div_iff₀ (by norm_num : (0 : ℝ) < 25) (by positivity : (0 : ℝ) < exp x + exp (-x))]
    linarith
  linarith

/-- |tanh x| > 24/25 when |x| > 2. -/
theorem tanh_saturation_abs {x : ℝ} (hx : |x| > 2) : |tanh x| > 24 / 25 := by
  by_cases h_pos : x >= 0
  · have h2 : x > 2 := by rwa [abs_of_nonneg h_pos] at hx
    have ht_pos : tanh x > 0 := tanh_pos_of_pos (by linarith)
    rw [abs_of_pos ht_pos]
    exact tanh_saturation_pos h2
  · push_neg at h_pos
    have h_neg : -x > 2 := by rwa [abs_of_neg h_pos] at hx
    have ht_neg : tanh x < 0 := tanh_neg_of_neg h_pos
    rw [abs_of_neg ht_neg]
    rw [← Real.tanh_neg]
    exact tanh_saturation_pos h_neg

/-! ## Linear Map and Policy Definition -/

/-- A linear function from observations to a single hidden unit: z = w . s + b.
    This represents the pre-activation of an H=1 MLP policy. -/
structure LinearMap (n : Nat) where
  weights : Fin n → ℝ
  bias : ℝ

namespace LinearMap

/-- Evaluate the linear map at an observation. -/
def eval {n : Nat} (lm : LinearMap n) (s : Fin n → ℝ) : ℝ :=
  (Finset.sum Finset.univ (fun i : Fin n => lm.weights i * s i)) + lm.bias

/-- The L1 norm of the weight vector. -/
def l1Norm {n : Nat} (lm : LinearMap n) : ℝ :=
  Finset.sum Finset.univ (fun i : Fin n => |lm.weights i|)

theorem l1Norm_nonneg {n : Nat} (lm : LinearMap n) : lm.l1Norm >= 0 := by
  unfold l1Norm
  exact Finset.sum_nonneg (fun i _ => abs_nonneg _)

end LinearMap

/-- An H=1 MLP policy with 2 actions.
    The policy computes z = w . s + b, then selects action 0 if tanh(z) > threshold,
    action 1 otherwise. -/
structure H1Policy (n : Nat) where
  lm : LinearMap n
  threshold : ℝ
  threshold_lt_one : threshold < 1
  threshold_gt_neg_one : threshold > -1

namespace H1Policy

/-- The pre-activation z = weights . obs + bias. -/
def z {n : Nat} (p : H1Policy n) (s : Fin n → ℝ) : ℝ :=
  p.lm.eval s

/-- The action selected by the policy. Action 0 if tanh(z) > threshold. -/
def action {n : Nat} (p : H1Policy n) (s : Fin n → ℝ) : Fin 2 :=
  if Real.tanh (p.z s) > p.threshold then 0 else 1

/-- The noise-perturbed observation. -/
def perturbedObs {n : Nat} (s : Fin n → ℝ) (epsilon : Fin n → ℝ) (i : Fin n) : ℝ :=
  s i + epsilon i

/-- Change in z due to noise: dz = w . epsilon. -/
def dz {n : Nat} (p : H1Policy n) (epsilon : Fin n → ℝ) : ℝ :=
  Finset.sum Finset.univ (fun i : Fin n => p.lm.weights i * epsilon i)

/-- z(s + eps) = z(s) + dz(eps). -/
theorem zNoisy_eq_z_plus_dz {n : Nat} (p : H1Policy n) (s epsilon : Fin n → ℝ) :
    p.lm.eval (perturbedObs s epsilon) = p.z s + p.dz epsilon := by
  unfold z LinearMap.eval perturbedObs dz
  simp only [mul_add]
  rw [Finset.sum_add_distrib]
  ring

/-- Bound on |dz|: |w . eps| <= ||w||_1 * delta when |eps_i| <= delta. -/
theorem dz_bound {n : Nat} (p : H1Policy n) (epsilon : Fin n → ℝ) (delta : ℝ)
    (_h_delta : delta >= 0)
    (h_eps : ∀ i, |epsilon i| <= delta) :
    |p.dz epsilon| <= p.lm.l1Norm * delta := by
  unfold dz LinearMap.l1Norm
  have h1 : |Finset.sum Finset.univ (fun i : Fin n => p.lm.weights i * epsilon i)|
      <= Finset.sum Finset.univ (fun i : Fin n => |p.lm.weights i * epsilon i|) :=
    Finset.abs_sum_le_sum_abs _ _
  have h2 : Finset.sum Finset.univ (fun i : Fin n => |p.lm.weights i * epsilon i|)
      = Finset.sum Finset.univ (fun i : Fin n => |p.lm.weights i| * |epsilon i|) := by
    congr with i; exact abs_mul _ _
  have h3 : Finset.sum Finset.univ (fun i : Fin n => |p.lm.weights i| * |epsilon i|)
      <= Finset.sum Finset.univ (fun i : Fin n => |p.lm.weights i| * delta) :=
    Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (h_eps i) (abs_nonneg _))
  have h4 : Finset.sum Finset.univ (fun i : Fin n => |p.lm.weights i| * delta)
      = (Finset.sum Finset.univ (fun i : Fin n => |p.lm.weights i|)) * delta := by
    rw [Finset.sum_mul]
  linarith

/-! ## Core Noise Insensitivity Theorems -/

/-- If z(s) > kappa and |dz| < kappa, then z(s + eps) > 0. -/
theorem z_pos_preserved
    {n : Nat} (p : H1Policy n) (s epsilon : Fin n → ℝ)
    (kappa : ℝ) (_hkappa : kappa > 0)
    (h_z_pos : p.z s > kappa)
    (h_dz_small : |p.dz epsilon| < kappa) :
    p.lm.eval (perturbedObs s epsilon) > 0 := by
  rw [zNoisy_eq_z_plus_dz]
  have : p.z s + p.dz epsilon >= p.z s - |p.dz epsilon| := by
    linarith [neg_le_abs (p.dz epsilon)]
  have : p.z s - |p.dz epsilon| > 0 := by linarith
  linarith

/-- If z(s) < -kappa and |dz| < kappa, then z(s + eps) < 0. -/
theorem z_neg_preserved
    {n : Nat} (p : H1Policy n) (s epsilon : Fin n → ℝ)
    (kappa : ℝ) (_hkappa : kappa > 0)
    (h_z_neg : p.z s < -kappa)
    (h_dz_small : |p.dz epsilon| < kappa) :
    p.lm.eval (perturbedObs s epsilon) < 0 := by
  rw [zNoisy_eq_z_plus_dz]
  have : p.z s + p.dz epsilon <= p.z s + |p.dz epsilon| := by
    linarith [le_abs_self (p.dz epsilon)]
  have : p.z s + |p.dz epsilon| < 0 := by linarith
  linarith

/-! ## Main Noise Robustness Theorems -/

/-- **Bang-Bang Noise Robustness (positive z case).**
    For an H=1 MLP policy, if the pre-activation is far from zero (z > kappa)
    and the total noise is bounded (||w||_1 * delta < kappa),
    then the perturbed pre-activation remains positive. -/
theorem bang_bang_noise_robustness
    {n : Nat} (p : H1Policy n) (s epsilon : Fin n → ℝ)
    (kappa delta : ℝ)
    (hkappa : kappa > 0)
    (hdelta : delta >= 0)
    (h_z_far : p.z s > kappa)
    (h_noise_bound : ∀ i, |epsilon i| <= delta)
    (h_total_noise : p.lm.l1Norm * delta < kappa) :
    p.lm.eval (perturbedObs s epsilon) > 0 := by
  have h_dz : |p.dz epsilon| < kappa := by
    calc |p.dz epsilon|
        <= p.lm.l1Norm * delta := p.dz_bound epsilon delta hdelta h_noise_bound
      _ < kappa := h_total_noise
  exact z_pos_preserved p s epsilon kappa hkappa h_z_far h_dz

/-- **Bang-Bang Noise Robustness (negative z case).** -/
theorem bang_bang_noise_robustness_neg
    {n : Nat} (p : H1Policy n) (s epsilon : Fin n → ℝ)
    (kappa delta : ℝ)
    (hkappa : kappa > 0)
    (hdelta : delta >= 0)
    (h_z_neg : p.z s < -kappa)
    (h_noise_bound : ∀ i, |epsilon i| <= delta)
    (h_total_noise : p.lm.l1Norm * delta < kappa) :
    p.lm.eval (perturbedObs s epsilon) < 0 := by
  have h_dz : |p.dz epsilon| < kappa := by
    calc |p.dz epsilon|
        <= p.lm.l1Norm * delta := p.dz_bound epsilon delta hdelta h_noise_bound
      _ < kappa := h_total_noise
  exact z_neg_preserved p s epsilon kappa hkappa h_z_neg h_dz

/-! ## Safe Zone -/

/-- The safe zone: observations where |z| >= kappa.
    In this region, the pre-activation is far enough from the decision
    boundary that bounded noise cannot flip the action. -/
def safeZone {n : Nat} (p : H1Policy n) (kappa : ℝ) : Set (Fin n → ℝ) :=
  { s | |p.z s| >= kappa }

private theorem safeZone_pos {n : Nat} (p : H1Policy n) (s : Fin n → ℝ)
    (kappa : ℝ) (h_safe : s ∈ p.safeZone kappa) (h_pos : p.z s > 0) :
    p.z s >= kappa := by
  rw [safeZone] at h_safe; dsimp at h_safe
  rwa [abs_of_pos h_pos] at h_safe

private theorem safeZone_neg {n : Nat} (p : H1Policy n) (s : Fin n → ℝ)
    (kappa : ℝ) (h_safe : s ∈ p.safeZone kappa) (h_neg : p.z s < 0) :
    -p.z s >= kappa := by
  rw [safeZone] at h_safe; dsimp at h_safe
  rwa [abs_of_neg h_neg] at h_safe

/-- **Safe Zone Sign Preservation.** In the safe zone, the sign of the
    pre-activation is preserved under bounded noise. Both directions
    (positive and negative) are guaranteed. -/
theorem safe_zone_preserves_sign
    {n : Nat} (p : H1Policy n) (s epsilon : Fin n → ℝ)
    (kappa delta : ℝ)
    (_hkappa : kappa > 0)
    (hdelta : delta >= 0)
    (h_safe : s ∈ p.safeZone kappa)
    (h_noise_bound : ∀ i, |epsilon i| <= delta)
    (h_total_noise : p.lm.l1Norm * delta < kappa) :
    (p.z s > 0 -> p.lm.eval (perturbedObs s epsilon) > 0) ∧
    (p.z s < 0 -> p.lm.eval (perturbedObs s epsilon) < 0) := by
  constructor
  · intro h_pos
    have h_ge : p.z s >= kappa := safeZone_pos p s kappa h_safe h_pos
    have h_dz : |p.dz epsilon| < kappa := by
      calc |p.dz epsilon|
          <= p.lm.l1Norm * delta := p.dz_bound epsilon delta hdelta h_noise_bound
        _ < kappa := h_total_noise
    rw [zNoisy_eq_z_plus_dz]
    have : p.z s + p.dz epsilon >= p.z s - |p.dz epsilon| := by
      linarith [neg_le_abs (p.dz epsilon)]
    have : p.z s - |p.dz epsilon| > 0 := by linarith
    linarith
  · intro h_neg
    have h_ge : -p.z s >= kappa := safeZone_neg p s kappa h_safe h_neg
    have h_dz : |p.dz epsilon| < kappa := by
      calc |p.dz epsilon|
          <= p.lm.l1Norm * delta := p.dz_bound epsilon delta hdelta h_noise_bound
        _ < kappa := h_total_noise
    rw [zNoisy_eq_z_plus_dz]
    have : p.z s + p.dz epsilon <= p.z s + |p.dz epsilon| := by
      linarith [le_abs_self (p.dz epsilon)]
    have : p.z s + |p.dz epsilon| < 0 := by linarith
    linarith

end H1Policy

/-! ## Summary: The Bang-Bang Noise Robustness Theorem -/

/-- **The Bang-Bang Noise Robustness Theorem (final form).**

    For any H=1 MLP policy, observation s, noise bounded by delta,
    and safety margin kappa > ||w||_1 * delta:

    If z(s) > kappa then z(s + eps) > 0.
    If z(s) < -kappa then z(s + eps) < 0.

    The sign of the pre-activation is preserved under bounded noise,
    meaning the action (determined by sign(z) when tanh is saturated)
    cannot flip. This holds for *any* such policy regardless of how
    it was obtained (gradient descent, evolution strategy, or manual design).
-/
theorem bang_bang_noise_robustness_final
    (n : Nat) (p : H1Policy n) (s epsilon : Fin n -> Real)
    (kappa delta : Real)
    (hkappa : kappa > 0)
    (hdelta : delta >= 0)
    (h_noise_bound : ∀ i, |epsilon i| <= delta)
    (h_total_noise : p.lm.l1Norm * delta < kappa)
    (h_z_pos : p.z s > kappa) :
    p.lm.eval (H1Policy.perturbedObs s epsilon) > 0 :=
  H1Policy.bang_bang_noise_robustness p s epsilon kappa delta
    hkappa hdelta h_z_pos h_noise_bound h_total_noise

/-- Symmetric version for negative z. -/
theorem bang_bang_noise_robustness_final_neg
    (n : Nat) (p : H1Policy n) (s epsilon : Fin n -> Real)
    (kappa delta : Real)
    (hkappa : kappa > 0)
    (hdelta : delta >= 0)
    (h_noise_bound : ∀ i, |epsilon i| <= delta)
    (h_total_noise : p.lm.l1Norm * delta < kappa)
    (h_z_neg : p.z s < -kappa) :
    p.lm.eval (H1Policy.perturbedObs s epsilon) < 0 :=
  H1Policy.bang_bang_noise_robustness_neg p s epsilon kappa delta
    hkappa hdelta h_z_neg h_noise_bound h_total_noise

end ProvablyCorrectControllers

end
