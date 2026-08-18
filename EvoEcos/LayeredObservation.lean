/-
Layered Observation Composition
================================

When multiple observation functions are combined (e.g., source code +
bytecode + traces), the composed observation is at least as informative
as any individual layer. This file proves the monotonicity of observation
enrichment: the composed observation (obs₁, obs₂) is a refinement of
either individual layer, meaning it distinguishes at least as many worlds.

Key insight: (obs₁, obs₂) w1 = (obs₁, obs₂) w2 implies BOTH obs₁ w1 = obs₁ w2
AND obs₂ w1 = obs₂ w2. So the composed observation's kernel is a SUBSET of
each individual kernel. This means:
  - Architectural under either layer ⟹ architectural under composition
  - Counterfactual under composition ⟹ counterfactual under BOTH layers

The disagreement set from observation_scarcity_spec.md is monotonically
non-increasing under observation enrichment.

Results (0 sorry):
  1. architectural_fst_preserved — architectural under layer 1 preserved under composition
  2. architectural_snd_preserved — architectural under layer 2 preserved under composition
  3. counterfactual_composed_implies_counterfactual_fst — counterfactual under
     composition implies counterfactual under layer 1
  4. counterfactual_composed_implies_counterfactual_snd — counterfactual under
     composition implies counterfactual under layer 2
  5. disagreement_monotone_fst — disagreement under composition ⊆ disagreement under layer 1
  6. disagreement_monotone_snd — disagreement under composition ⊆ disagreement under layer 2
-/

import EvoEcos.ACD

namespace EvoEcos

open ObservationalSetup

/-! ## Composed Observation

Given two observation functions `obs₁ : W → O₁` and `obs₂ : W → O₂`,
the composed observation maps each world to the pair of both observations.
This models layered audit: (source code, bytecode), or (source, traces). -/

/-- Composed observation: maps each world to both observations simultaneously. -/
def composedObs {W : Type} (obs₁ : W → α) (obs₂ : W → β) : W → α × β :=
  fun w => (obs₁ w, obs₂ w)

/-- The observational setup using a composed observation. -/
def layeredSetup {W O₁ O₂ : Type}
    (obs₁ : W → O₁) (obs₂ : W → O₂) (truth : W → Bool) :
    ObservationalSetup W (O₁ × O₂) where
  obs := composedObs obs₁ obs₂
  truth := truth

/-! ## Architectural Preservation

If a predicate is architectural under an individual layer, it remains
architectural under composition. Adding more observation channels cannot
break what an existing layer already resolves.

Proof idea: If (obs₁, obs₂) w1 = (obs₁, obs₂) w2, then in particular
obs₁ w1 = obs₁ w2 (by projection). If P is architectural under obs₁,
then truth w1 = truth w2. -/

/-- If P is architectural under the first layer, it is architectural
under the composed observation. -/
theorem architectural_fst_preserved {W O₁ O₂ : Type}
    (obs₁ : W → O₁) (obs₂ : W → O₂) (truth : W → Bool)
    (h : ∀ w1 w2, obs₁ w1 = obs₁ w2 → truth w1 = truth w2) :
    (layeredSetup obs₁ obs₂ truth).Architectural := by
  intro w1 w2 h_comp
  simp [layeredSetup, composedObs] at h_comp
  exact h w1 w2 h_comp.1

/-- If P is architectural under the second layer, it is architectural
under the composed observation. -/
theorem architectural_snd_preserved {W O₁ O₂ : Type}
    (obs₁ : W → O₁) (obs₂ : W → O₂) (truth : W → Bool)
    (h : ∀ w1 w2, obs₂ w1 = obs₂ w2 → truth w1 = truth w2) :
    (layeredSetup obs₁ obs₂ truth).Architectural := by
  intro w1 w2 h_comp
  simp [layeredSetup, composedObs] at h_comp
  exact h w1 w2 h_comp.2

/-! ## Counterfactual Monotonicity

Contrapositive of preservation: if P is counterfactual under composition,
it must be counterfactual under EACH individual layer.

Proof: If (obs₁, obs₂) w1 = (obs₁, obs₂) w2 ∧ truth w1 ≠ truth w2,
then obs₁ w1 = obs₁ w2 ∧ truth w1 ≠ truth w2 (by projection). -/

/-- If P is counterfactual under the composed observation, it is
counterfactual under the first layer. -/
theorem counterfactual_composed_implies_counterfactual_fst {W O₁ O₂ : Type}
    (obs₁ : W → O₁) (obs₂ : W → O₂) (truth : W → Bool)
    (h_comp : (layeredSetup obs₁ obs₂ truth).Counterfactual) :
    ∃ w1 w2, obs₁ w1 = obs₁ w2 ∧ truth w1 ≠ truth w2 := by
  obtain ⟨w1, w2, h_obs, h_truth⟩ := h_comp
  simp [layeredSetup, composedObs] at h_obs
  exact ⟨w1, w2, h_obs.1, h_truth⟩

/-- If P is counterfactual under the composed observation, it is
counterfactual under the second layer. -/
theorem counterfactual_composed_implies_counterfactual_snd {W O₁ O₂ : Type}
    (obs₁ : W → O₁) (obs₂ : W → O₂) (truth : W → Bool)
    (h_comp : (layeredSetup obs₁ obs₂ truth).Counterfactual) :
    ∃ w1 w2, obs₂ w1 = obs₂ w2 ∧ truth w1 ≠ truth w2 := by
  obtain ⟨w1, w2, h_obs, h_truth⟩ := h_comp
  simp [layeredSetup, composedObs] at h_obs
  exact ⟨w1, w2, h_obs.2, h_truth⟩

/-! ## Disagreement Set Inclusion

The disagreement set D(P, obs) = {(w1, w2) | obs w1 = obs w2 ∧ P w1 ≠ P w2}
from observation_scarcity_spec.md. Under composition:

  D(P, (obs₁, obs₂)) ⊆ D(P, obs₁)
  D(P, (obs₁, obs₂)) ⊆ D(P, obs₂)

because (obs₁, obs₂) w1 = (obs₁, obs₂) w2 implies obsᵢ w1 = obsᵢ w2. -/

/-- Disagreement under composition implies disagreement under layer 1. -/
theorem disagreement_monotone_fst {W O₁ O₂ : Type}
    (obs₁ : W → O₁) (obs₂ : W → O₂) (truth : W → Bool)
    (w1 w2 : W)
    (h_comp : (obs₁ w1, obs₂ w1) = (obs₁ w2, obs₂ w2))
    (h_truth : truth w1 ≠ truth w2) :
    obs₁ w1 = obs₁ w2 ∧ truth w1 ≠ truth w2 :=
  ⟨congrArg Prod.fst h_comp, h_truth⟩

/-- Disagreement under composition implies disagreement under layer 2. -/
theorem disagreement_monotone_snd {W O₁ O₂ : Type}
    (obs₁ : W → O₁) (obs₂ : W → O₂) (truth : W → Bool)
    (w1 w2 : W)
    (h_comp : (obs₁ w1, obs₂ w1) = (obs₁ w2, obs₂ w2))
    (h_truth : truth w1 ≠ truth w2) :
    obs₂ w1 = obs₂ w2 ∧ truth w1 ≠ truth w2 :=
  ⟨congrArg Prod.snd h_comp, h_truth⟩

end EvoEcos
