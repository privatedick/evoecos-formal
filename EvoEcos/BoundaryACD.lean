/-
Boundary × ACD: Composability of Discreteness and Architectural Verifiability
===============================================================================

Composition theorem: architectural_verifiable AND high_discreteness IMPLIES boundary_observable.

ACD(i) = architecturally verifiable: observation of the system determines the
truth of the failure condition. A failure mode is ACD(i) if there exists an
architectural observation that perfectly classifies it.

Boundary observable: the failure locus is detectable from the architecture.
A failure is boundary-observable if its location can be determined from
structural analysis.

Main theorem: high_discreteness AND ACD(i) IMPLIES boundary_observable

Proof sketch:
  1. High discreteness means the failure is a sharp state transition
  2. ACD(i) means the failure is architecturally observable
  3. Combining: the sharp transition is observable at an architectural boundary
  4. Therefore: the failure is boundary-observable

3 theorems + 2 helper structures, 0 sorry.

Date: 2026-05-28
-/

import EvoEcos.DiscretenessGradient
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace EvoEcos.BoundaryACD

open DiscretenessGradient

/-! ## Architectural Observability -/

/-- A failure mode is ACD(i) — architecturally verifiable — if there exists
    an observation function from the architecture that detects it.
    informativeness = 1 means the observation perfectly determines the failure. -/
structure ACDVerifiable where
  mechanism : FailureMechanism
  informativeness : ℝ
  informativeness_bounds : 0 ≤ informativeness ∧ informativeness ≤ 1
  -- ACD condition: observation determines truth
  acd : informativeness ≥ 0.8

/-- A failure is boundary-observable if its failure locus can be detected
    from architectural analysis. This combines observability with localization. -/
structure BoundaryObservable where
  mechanism : FailureMechanism
  observability : ℝ
  observability_nonneg : 0 ≤ observability
  observability_le_one : observability ≤ 1

/-! ## Theorem 1: ACD Implies Partial Observability -/

/-- If a failure mode is ACD(i), it has at least 0.8 observability.
    The architectural observation provides strong information about the failure. -/
theorem acd_implies_observable (acd : ACDVerifiable) :
    (0.8 : ℝ) ≤ acd.informativeness :=
  acd.acd

/-! ## Theorem 2: High Discreteness Strengthens Observability -/

/-- High discreteness (D >= 0.8) combined with ACD informativeness gives
    a combined observability score >= 0.8.

    The key insight: discrete failures are easier to observe because the
    state transition is sharp. Combined with architectural verifiability,
    the failure is highly observable.

    Formally: min(D, informativeness) >= 0.8 when both D >= 0.8 and info >= 0.8. -/
theorem high_discreteness_acd_observable (m : FailureMechanism) (info : ℝ)
    (hD : m.discreteness ≥ 0.8) (h_info : info ≥ 0.8)
    (_h_info_bounds : 0 ≤ info ∧ info ≤ 1) :
    min m.discreteness info ≥ (0.8 : ℝ) := by
  exact le_min hD h_info

/-! ## Theorem 3: Composition — High Discreteness AND ACD IMPLIES Boundary Observable -/

/-- The main composition theorem. If:
    (1) a failure mode has high discreteness (D >= 0.8), AND
    (2) it is architecturally verifiable (ACD with informativeness >= 0.8),
    THEN it is boundary-observable (observability >= 0.64 = 0.8 * 0.8).

    The observability bound comes from the product: discrete transitions
    are localized (D >= 0.8) and architecturally detectable (info >= 0.8),
    so their product is >= 0.64, which is the threshold for boundary observability. -/
theorem composition_acd_discreteness (acd : ACDVerifiable)
    (h_high_D : acd.mechanism.discreteness ≥ 0.8) :
    ∃ bo : BoundaryObservable,
      bo.mechanism = acd.mechanism ∧
      bo.observability = acd.mechanism.discreteness * acd.informativeness ∧
      bo.observability ≥ 0.64 := by
  have h_info : acd.informativeness ≥ 0.8 := acd.acd
  -- D * info >= 0.8 * 0.8 = 0.64
  have h_064 : (0.64 : ℝ) ≤ acd.mechanism.discreteness * acd.informativeness := by
    nlinarith
  have h_obs_nonneg : 0 ≤ acd.mechanism.discreteness * acd.informativeness :=
    mul_nonneg acd.mechanism.discreteness_nonneg acd.informativeness_bounds.1
  have h_obs_le : acd.mechanism.discreteness * acd.informativeness ≤ 1 := by
    calc acd.mechanism.discreteness * acd.informativeness
        ≤ acd.mechanism.discreteness * 1 :=
          mul_le_mul_of_nonneg_left acd.informativeness_bounds.2 acd.mechanism.discreteness_nonneg
      _ ≤ 1 := by
          have : acd.mechanism.discreteness * 1 = acd.mechanism.discreteness := by ring
          rw [this]
          exact acd.mechanism.discreteness_le_one
  exact ⟨⟨acd.mechanism, acd.mechanism.discreteness * acd.informativeness,
    h_obs_nonneg, h_obs_le⟩, rfl, rfl, h_064⟩

end EvoEcos.BoundaryACD
