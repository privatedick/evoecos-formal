/-
Safety–Diversification Duality
================================

The wall is in superposition: both safety shield and ecological boundary.
This file formalizes the duality by pairing each safety theorem with its
diversification analog, proving they coexist without contradiction.

The "measurement problem" is real: the same data projects differently
depending on the lens. NoCollapse is safety; output_bottleneck is
diversification. Both are theorems of the same system.

Safety:    ~20 theorems, 0 sorry
Diversification: 20 theorems, 0 sorry
Duality:   this file — formal pairing and superposition proofs
-/

import EvoEcos.Diversification
import EvoEcos.Layers
import EvoEcos.Convergence
import EvoEcos.WallDomainTriple

noncomputable section

namespace EvoEcos.Duality

/-! ## Duality Pairing Type -/

/-- A duality pair: one safety theorem and one diversification theorem
    that describe the same phenomenon from different perspectives. -/
structure DualPair where
  safetyName : String
  diversificationName : String
  description : String
  -- The wall exhibits both properties simultaneously
  -- (formalized by the theorems being independently provable)

/-! ## The Duality Catalog -/

def outputBottleneck_noCollapse : DualPair where
  safetyName := "noCollapse (L1State.stability > 0)"
  diversificationName := "output_bottleneck (entropy ≤ nActions)"
  description := "L1 has non-trivial content ⟷ strategy produces bounded outputs"

def convergenceCriterion_minimalForm : DualPair where
  safetyName := "convergence_criterion"
  diversificationName := "minimalFormBound / output_bottleneck"
  description := "Convergence to stable state ⟷ convergence to minimal automaton"

def wallBlocksL3_diversificationActive : DualPair where
  safetyName := "wallBlocksL3"
  diversificationName := "diversificationActive"
  description := "Wall blocks L3 plans ⟷ wall forces L1 independence"

def wallBenefit_wallBenefitRequiresNiche : DualPair where
  safetyName := "wallBenefit_pos_iff_triple"
  diversificationName := "wallBenefitRequiresDistinctNiche"
  description := "Wall helps iff triple holds ⟷ wall helps iff niche exists"

def l1Independent_l1StrategyIndependent : DualPair where
  safetyName := "L1IndependentOfL3"
  diversificationName := "l1StrategyIndependentOfL3"
  description := "L1 reflex independent of L3 ⟷ L1 strategy independent of L3"

def convergencePreserved_isolationPreserved : DualPair where
  safetyName := "convergence_preserved_by_nonL1_transition"
  diversificationName := "isolationPreservesNiche"
  description := "Non-L1 transitions preserve convergence ⟷ preserve niche"

def l3CannotBypass_l3CannotBypassNiche : DualPair where
  safetyName := "L3CannotBypassWall"
  diversificationName := "l3CannotBypassNicheBoundary"
  description := "L3 cannot bypass wall ⟷ L3 cannot bypass niche boundary"

def wallActivates_wallCreatesIsolation : DualPair where
  safetyName := "wall_activates_when_unstable"
  diversificationName := "wallActivationCreatesIsolation"
  description := "Wall activates when L1 unstable ⟷ wall creates niche isolation"

/-! ## Superposition Theorems

These prove that safety and diversification properties COEXIST —
the same system state satisfies both perspectives simultaneously.
-/

/-- The fundamental superposition: L1 has both safety (noCollapse) and
    diversification (output_bottleneck) properties simultaneously.
    This is not a contradiction — it is a duality. -/
theorem safety_diversification_coexist {obsDim actions : Nat}
    (σ : Diversification.Strategy obsDim actions) (s : SystemState)
    (h_active : s.l1.active = true)
    (h_nc : L1State.noCollapse s.l1) :
    -- Safety: L1 has non-trivial content
    Diversification.HasBehavioralContent s.l1 ∧
    -- Diversification: strategy is bounded
    Diversification.strategyEntropy σ ≤ actions := by
  exact ⟨⟨h_active, h_nc⟩, Diversification.output_bottleneck σ⟩

/-- Wall superposition: wall simultaneously blocks L3 (safety) and
    forces niche independence (diversification). -/
theorem wall_superposition (s : SystemState)
    (h_wall : s.l2.wall = true)
    (h_active : s.l1.active = true)
    (h_nc : L1State.noCollapse s.l1) :
    -- Safety: L3 cannot plan
    ¬L3State.canPlan s.l3 s.l2 ∧
    -- Diversification: L1 maintains independent niche
    ¬L3State.canPlan s.l3 s.l2 ∧ s.l1.canReflex := by
  have h_safety : ¬L3State.canPlan s.l3 s.l2 := by
    intro h_plan
    unfold L3State.canPlan at h_plan
    exact h_plan.2.2 h_wall
  have h_div : ¬L3State.canPlan s.l3 s.l2 ∧ s.l1.canReflex :=
    Diversification.nicheIndependenceUnderWall s h_wall h_active h_nc
  exact ⟨h_safety, h_div⟩

/-- Preservation superposition: non-L1 transitions simultaneously
    preserve safety invariants (convergence) and niche state. -/
theorem preservation_superposition (s1 s2 : SystemState) (t : Transition.TransKind)
    (h_step : Transition.isValidStep ⟨s1, s2, t⟩)
    (h_nonL1 : ¬ t.affectsL1) :
    -- Both safety and diversification agree: L1 state is untouched
    s2.l1 = s1.l1 := by
  exact Diversification.isolationPreservesNiche s1 s2 t h_step h_nonL1

end EvoEcos.Duality

end
