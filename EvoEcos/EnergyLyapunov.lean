/-
Energy-Lyapunov Certificate
===========================

A storage-function / Lyapunov certificate (Willems-style dissipativity, adapted
to the discrete L1 dynamics) for the L1 energy budget.

The *destabilizing* quantity — stress σ — acts as a Lyapunov function: it is
nonnegative, non-increasing under `maintainStability`, and contracts to 0. Its
sublevel set {σ < 0.3} is *exactly* the energetically self-sustaining regime,
where energy intake strictly exceeds the homeostatic cost (positive balance).
Hence the Lyapunov descent of stress drives L1, in finite time, into a regime
that simultaneously replenishes its energy budget and preserves `NoCollapse`.

This composes (does not re-prove) four existing results:
  - NoStrangeAttractor.stress_contraction / .stress_contraction_strict
  - NoStrangeAttractor.stress_converges_to_zero
  - NoStrangeAttractor.stability_non_decreasing_maintain
  - L1EnergySufficiency.balance_positive_low_stress

Downstream consumer: maintain_energy_budget() runtime + the NoCollapse proof
certificate (Layers.L1State.noCollapse).
-/

import EvoEcos.Layers
import EvoEcos.L1EnergySufficiency
import EvoEcos.NoStrangeAttractor
import Mathlib.Data.Real.Basic

noncomputable section

namespace EvoEcos.EnergyLyapunov

open EvoEcos.NoStrangeAttractor

/-! ## 1. Stress as a Lyapunov function

A discrete Lyapunov function `V : L1State → ℝ` must be positive semi-definite and
non-increasing along the dynamics, with strict descent away from the equilibrium.
Stress satisfies all three. -/

/-- The Lyapunov function for L1: the destabilizing stress level. -/
def V (s : L1State) : ℝ := s.stress.val

/-- (Lyapunov 1) Positive semi-definite: `V ≥ 0` everywhere. -/
theorem V_nonneg (s : L1State) : 0 ≤ V s := s.stress.property.1

/-- (Lyapunov 2) Non-increasing along the flow: `V (f s) ≤ V s`. -/
theorem V_decreasing (s : L1State) : V (L1State.maintainStability s) ≤ V s := by
  unfold V
  have h := stress_contraction s
  have hσ := s.stress.property.1
  linarith [h, hσ]

/-- (Lyapunov 3) Strict descent away from the equilibrium `σ = 0`. -/
theorem V_strict_decrease (s : L1State) (h : 0 < V s) :
    V (L1State.maintainStability s) < V s :=
  stress_contraction_strict s h

/-! ## 2. The sustainable sublevel set {V < 0.3}

The sublevel set of the Lyapunov function below the sustainability threshold
coincides with the regime where the energy budget is in surplus. -/

/-- Energy balance: intake minus total homeostatic cost. -/
def energyBalance (s : L1State) : ℝ := 10 / 100 - L1State.homeostaticTotal s

/-- Inside the Lyapunov sublevel set {σ < 0.3}, the energy balance is strictly
    positive: intake exceeds the homeostatic cost. This is the energetic meaning
    of the Lyapunov sublevel set. -/
theorem balance_pos_in_sublevel (s : L1State) (h : s.stress.val < 3 / 10) :
    0 < energyBalance s := by
  unfold energyBalance L1State.homeostaticTotal homeostaticCost stressCostCoeff
  have hb := L1State.balance_positive_low_stress s h
  linarith [hb]

/-! ## 3. Finite-time descent into the sustainable set -/

/-- The Lyapunov descent of stress drives L1, from ANY initial state, into the
    energetically self-sustaining regime in finite time: there is a horizon `N`
    after which every iterate has strictly positive energy balance. -/
theorem reaches_sustainable (s : L1State) :
    ∃ N : Nat, ∀ n ≥ N, 0 < energyBalance (iterateMaintainStability n s) := by
  obtain ⟨N, hN⟩ := stress_converges_to_zero s (3 / 10) (by norm_num)
  exact ⟨N, fun n hn => balance_pos_in_sublevel _ (hN n hn)⟩

/-! ## 4. NoCollapse is preserved along the descent -/

/-- Stability along the iterated dynamics never drops below its initial value
    (monotone lift of `stability_non_decreasing_maintain` to all iterates). -/
theorem stability_iter_ge (s : L1State) :
    ∀ n, s.stability.val ≤ (iterateMaintainStability n s).stability.val := by
  intro n
  induction n with
  | zero => simp [iterateMaintainStability]
  | succ n ih =>
    have step := stability_non_decreasing_maintain (iterateMaintainStability n s)
    simp only [iterateMaintainStability]
    linarith [ih, step]

/-! ## 5. Capstone: the energy-Lyapunov certificate -/

/-- **Energy-Lyapunov certificate.** From any live L1 state (`noCollapse`), the
    stress Lyapunov function certifies a finite horizon `N` after which the system
    is *permanently* energetically self-sustaining (strictly positive energy
    balance) while `NoCollapse` is preserved (stability stays positive). One
    Lyapunov function discharges both the budget guarantee and the safety
    invariant. -/
theorem energy_lyapunov_certificate (s : L1State) (h_alive : L1State.noCollapse s) :
    ∃ N : Nat, ∀ n ≥ N,
      0 < energyBalance (iterateMaintainStability n s)
      ∧ L1State.noCollapse (iterateMaintainStability n s) := by
  obtain ⟨N, hN⟩ := reaches_sustainable s
  refine ⟨N, fun n hn => ⟨hN n hn, ?_⟩⟩
  unfold L1State.noCollapse at h_alive ⊢
  linarith [stability_iter_ge s n, h_alive]

end EvoEcos.EnergyLyapunov
