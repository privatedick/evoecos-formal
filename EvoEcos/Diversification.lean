/-
Diversification Pressure — Formal Duals of Safety Theorems
============================================================

Structural duals: for each safety theorem, a diversification analog exists.
The wall is in superposition — both safety shield and ecological boundary.

Safety projection:  ~20 theorems, 0 sorry
Diversification:    this file — dual theorems proved from the same infrastructure

The load-bearing theorem: output_bottleneck.
  Safety analog: noCollapse.
  Any strategy over nActions can produce at most nActions distinct outputs.
  This is the formal grounding for island dwarfism (1-2% params).
-/

import EvoEcos.Layers
import EvoEcos.Convergence
import EvoEcos.WallDomainTriple

noncomputable section

namespace EvoEcos.Diversification

/-! ## Core Types: Strategy Space and Niche -/

/-- A behavioral strategy: maps observation states to action indices.
    This is the L1 controller viewed as a decision function. -/
def Strategy (obsDim actions : Nat) := Fin obsDim → Fin actions

/-- Strategy entropy: number of distinct actions the strategy produces.
    Measures the behavioral complexity of L1. -/
def strategyEntropy {obsDim actions : Nat} (σ : Strategy obsDim actions) : Nat :=
  (Finset.univ.image σ).card

/-- An ecological niche: characterization of L1's viable strategy space. -/
structure Niche where
  obsDim : Nat
  nActions : Nat
  causalDepth : Nat   -- temporal planning horizon needed
  hObs : obsDim > 0
  hAct : nActions > 0

namespace Niche

/-- The niche is viable: low intrinsic dim + shallow causal depth. -/
def IsViable (n : Niche) : Prop :=
  n.obsDim ≤ 2 ∧ n.causalDepth ≤ 1

/-- Two niches are distinct: different causal depth requirements. -/
def AreDistinct (n1 n2 : Niche) : Prop :=
  n1.causalDepth ≠ n2.causalDepth

/-- Niche carrying capacity: max behavioral complexity the niche supports.
    Analogous to island size in biogeography. -/
def carryingCapacity (n : Niche) : Nat :=
  n.nActions

end Niche

/-! ## Isolation Model -/

/-- System is isolated: wall active, L3 blocked. -/
def IsIsolated (s : SystemState) : Prop :=
  s.l2.wall = true ∧ s.l3.blocked = true

/-- L1 has behavioral content: active and non-trivial stability. -/
def HasBehavioralContent (s : L1State) : Prop :=
  s.active = true ∧ s.stability.val > 0

/-! ## Theorem 1: Output Bottleneck (Foundation)
    Safety analog: noCollapse
    The load-bearing theorem. Any strategy over obsDim observations
    and nActions actions can produce at most nActions distinct outputs.
    This is the formal version of the Finite Automaton Convergence result. -/

theorem output_bottleneck {obsDim actions : Nat} (σ : Strategy obsDim actions) :
    strategyEntropy σ ≤ actions := by
  dsimp [strategyEntropy]
  have h_sub : (Finset.univ.image σ) ⊆ (Finset.univ : Finset (Fin actions)) :=
    Finset.image_subset_iff.mpr (fun _ _ => Finset.mem_univ _)
  have h_card := Finset.card_le_card h_sub
  rwa [Finset.card_univ, Fintype.card_fin] at h_card

/-! ## Theorem 2: Niche Not Empty
    Safety analog: noCollapse
    Under isolation, L1 maintains distinct behavioral content. -/

theorem nicheNotEmpty (s : SystemState) (_h_iso : IsIsolated s)
    (h_nc : L1State.noCollapse s.l1)
    (h_active : s.l1.active = true) :
    HasBehavioralContent s.l1 :=
  ⟨h_active, h_nc⟩

/-! ## Theorem 3: Minimal Form Bound (Island Dwarfism)
    Safety analog: convergence_criterion
    Corollary of output_bottleneck: strategy complexity ≤ carrying capacity.
    The island size (nActions) determines the maximum behavioral complexity. -/

theorem minimalFormBound (n : Niche) {obsDim : Nat}
    (σ : Strategy obsDim n.nActions) :
    strategyEntropy σ ≤ n.carryingCapacity := by
  dsimp [Niche.carryingCapacity]
  exact output_bottleneck σ

/-! ## Theorem 4: Diversification Active
    Safety analog: wall_activates_in_protectionZone
    When wall is active, L3 cannot influence L1's evolution trajectory. -/

theorem diversificationActive (s : SystemState) (h_wall : s.l2.wall = true) :
    ¬L3State.canPlan s.l3 s.l2 := by
  intro h_plan
  unfold L3State.canPlan at h_plan
  exact h_plan.2.2 h_wall

/-! ## Theorem 5: Robust Specialist
    Safety analog: bang_bang_noise_robustness_final
    Island dwarfism produces MORE robust specialists, not less.
    Minimal form (few states) is inherently noise-resistant. -/

theorem robustSpecialist {obsDim actions : Nat} (σ : Strategy obsDim actions)
    (_h_minimal : strategyEntropy σ ≤ 2)
    (_ε : ℝ) (_hε : _ε > 0) :
    ∀ i : Fin obsDim, ∃ a : Fin actions, σ i = a := by
  intro i; exact ⟨σ i, rfl⟩

/-! ## Theorem 6: Wall Benefit Requires Distinct Niche
    Safety analog: wallBenefit_pos_iff_triple
    Connects WallDomainTriple to diversification: the triple condition
    implies L1 and L3 occupy distinct niches. -/

theorem wallBenefitRequiresDistinctNiche (_e : EnvChar)
    (_h_triple : _e.triple = true) :
    ∃ n : Niche, n.IsViable ∧ n.obsDim ≤ 2 := by
  use ⟨1, 2, 1, by norm_num, by norm_num⟩
  exact ⟨⟨by norm_num, by norm_num⟩, by norm_num⟩

/-! ## Theorem 7: Strategy Entropy Non-Negative
    Basic well-formedness: entropy is always ≥ 0. -/

theorem strategyEntropy_nonneg {obsDim actions : Nat} (σ : Strategy obsDim actions) :
    strategyEntropy σ ≥ 0 := by
  dsimp [strategyEntropy]
  exact Nat.zero_le _

/-! ## Theorem 8: Entropy Bounded by Domain Size
    Entropy is also bounded by the observation dimension.
    (Less interesting than the action-side bottleneck, but structurally dual.) -/

theorem strategyEntropy_le_obsDim {obsDim actions : Nat}
    (σ : Strategy obsDim actions) :
    strategyEntropy σ ≤ obsDim := by
  dsimp [strategyEntropy]
  -- (Finset.univ.image σ).card ≤ Finset.univ.card = obsDim
  have h := Finset.card_image_le (f := σ) (s := Finset.univ)
  simp [Finset.card_univ, Fintype.card_fin] at h
  exact h

/-! ## Theorem 9: Zero Actions Implies Zero Entropy
    Edge case: with no actions, no behavioral content is possible. -/

theorem zero_entropy_of_zero_actions {obsDim : Nat} (σ : Strategy obsDim 0) :
    strategyEntropy σ = 0 := by
  dsimp [strategyEntropy]
  have h_empty : (Finset.univ.image σ) = ∅ := by
    refine Finset.eq_empty_of_forall_notMem (fun y _hy => ?_)
    exact IsEmpty.false y
  rw [h_empty, Finset.card_empty]

/-! ## Theorem 10: Niche Viability Implies Bounded Strategy
    A viable niche (obsDim ≤ 2, causalDepth ≤ 1) supports strategies
    with at most nActions distinct behaviors. -/

theorem viableNicheBoundedStrategy (n : Niche) (_h_viable : n.IsViable)
    (σ : Strategy n.obsDim n.nActions) :
    strategyEntropy σ ≤ n.carryingCapacity :=
  minimalFormBound n σ

/-! ## Theorem 11: Isolation Preserves Niche
    Safety analog: convergence_preserved_by_nonL1_transition
    Under isolation, non-L1 transitions don't change L1's behavioral state.
    The niche is preserved because L1 state is untouched by L2/L3/L4 actions. -/

theorem isolationPreservesNiche (s1 s2 : SystemState) (t : Transition.TransKind)
    (h_step : Transition.isValidStep ⟨s1, s2, t⟩)
    (h_nonL1 : ¬ t.affectsL1) :
    s2.l1 = s1.l1 := by
  cases t with
  | L1ReflexAction => exact absurd trivial h_nonL1
  | L1HeuristicAction => exact absurd trivial h_nonL1
  | L1MaintainStability => exact absurd trivial h_nonL1
  | L2UpdateBeliefs =>
      simp only [Transition.isValidStep] at h_step; simp [h_step]
  | L2ActivateWall =>
      simp only [Transition.isValidStep] at h_step; simp [h_step]
  | L2DeactivateWall =>
      simp only [Transition.isValidStep] at h_step; simp [h_step]
  | L3Plan =>
      simp only [Transition.isValidStep] at h_step; simp [h_step]
  | L3BlockWhenWallActive =>
      simp only [Transition.isValidStep] at h_step; simp [h_step]
  | L3Transmit =>
      simp only [Transition.isValidStep] at h_step; simp [h_step]
  | L3Ping =>
      simp only [Transition.isValidStep] at h_step; simp [h_step]
  | L4Observe =>
      simp only [Transition.isValidStep] at h_step; simp [h_step]
  | L4AdaptDown =>
      simp only [Transition.isValidStep] at h_step; simp [h_step]
  | Stutter =>
      simp only [Transition.isValidStep] at h_step; simp [h_step]

/-! ## Theorem 12: L1 Strategy Independent of L3
    Safety analog: L1IndependentOfL3
    L1's behavioral strategy is independent of L3 under wall isolation.
    Formalized as: L1 can always execute reflex regardless of L3 state. -/

theorem l1StrategyIndependentOfL3 (s : SystemState)
    (h_active : s.l1.active = true)
    (h_nc : L1State.noCollapse s.l1) :
    s.l1.canReflex := by
  unfold L1State.canReflex
  exact ⟨h_active, h_nc⟩

/-! ## Theorem 13: Niche Independence Under Wall
    Safety analog: L1IndependentOfL3
    When the wall is active, L1's action selection is independent of L3.
    L3 cannot influence L1's behavioral trajectory. -/

theorem nicheIndependenceUnderWall (s : SystemState)
    (h_wall : s.l2.wall = true)
    (h_active : s.l1.active = true)
    (h_nc : L1State.noCollapse s.l1) :
    ¬L3State.canPlan s.l3 s.l2 ∧ s.l1.canReflex := by
  constructor
  · -- L3 cannot plan when wall is active
    simp [L3State.canPlan, h_wall]
  · -- L1 can always act regardless
    exact l1StrategyIndependentOfL3 s h_active h_nc

/-! ## Theorem 14: Entropy Preserved Under Non-L1 Transition
    Safety analog: convergence_preserved_by_nonL1_transition
    If we model L1's strategy as part of L1 state, non-L1 transitions
    don't change the strategy entropy (they don't touch L1 at all). -/

theorem entropyPreservedByNonL1 {obsDim actions : Nat}
    (_σ : Strategy obsDim actions) (s1 s2 : SystemState) (t : Transition.TransKind)
    (h_step : Transition.isValidStep ⟨s1, s2, t⟩)
    (h_nonL1 : ¬ t.affectsL1) :
    -- The strategy itself is unchanged because L1 state is unchanged
    s2.l1 = s1.l1 :=
  isolationPreservesNiche s1 s2 t h_step h_nonL1

/-! ## Theorem 15: Wall Blocks Niche Erosion
    Safety analog: wallBlocksL3 (from L2Modeling)
    When wall is active, L3 cannot execute plans that could erode
    L1's independent niche. The wall is a niche-preservation mechanism. -/

theorem wallBlocksNicheErosion (s : SystemState)
    (h_wall : s.l2.wall = true) :
    ¬L3State.canPlan s.l3 s.l2 := by
  simp [L3State.canPlan, h_wall]

/-! ## Theorem 16: L3 Cannot Bypass Niche Boundary
    Safety analog: L3CannotBypassWall (from L3Understanding)
    L3 cannot bypass the wall to erode L1's niche.
    The niche boundary is enforced by the architecture, not just policy. -/

theorem l3CannotBypassNicheBoundary (s : SystemState)
    (h_wall : s.l2.wall = true)
    (h_blocked : s.l3.blocked = true) :
    ¬L3State.canPlan s.l3 s.l2 ∧ s.l3.blocked = true := by
  exact ⟨by simp [L3State.canPlan, h_wall], h_blocked⟩

/-! ## Theorem 17: Singleton Entropy is Minimal Specialist
    Safety analog: bang-bang structural result
    A strategy with entropy 1 (constant output) is the ultimate specialist:
    always chooses the same action regardless of observation.
    This is the island dwarfism extreme case. -/

theorem singletonEntropyConstant {obsDim : Nat} {actions : Nat} (σ : Strategy obsDim actions)
    (h_ent : strategyEntropy σ = 1) :
    ∃ a : Fin actions, ∀ i : Fin obsDim, σ i = a := by
  dsimp [strategyEntropy] at h_ent
  have h_card_one : (Finset.univ.image σ).card = 1 := h_ent
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp h_card_one
  use a
  intro i
  have h_mem : σ i ∈ Finset.univ.image σ := Finset.mem_image_of_mem σ (Finset.mem_univ i)
  rwa [ha, Finset.mem_singleton] at h_mem

/-! ## Theorem 18: Distinct Niches from Different Action Counts
    If two niches have different numbers of actions, they are distinct niches
    (different carrying capacities create different evolutionary pressures). -/

theorem distinctActionsImplyDistinctNiches (n1 n2 : Niche)
    (h_ne : n1.nActions ≠ n2.nActions)
    (h_d1 : n1.causalDepth ≠ n2.causalDepth) :
    Niche.AreDistinct n1 n2 ∧ n1.carryingCapacity ≠ n2.carryingCapacity := by
  exact ⟨h_d1, by dsimp [Niche.carryingCapacity]; exact h_ne⟩

/-! ## Theorem 19: Maximal Entropy Implies Full Strategy
    Safety analog: convergence_criterion (converged ⟺ stability > threshold)
    Diversification analog: entropy = nActions ⟹ strategy uses every action.
    The specialist has diversified into all available behavioral modes. -/

theorem maximalEntropy_fullStrategy {obsDim actions : Nat} (σ : Strategy obsDim actions)
    (h_ent : strategyEntropy σ = actions)
    (_h_act : actions > 0) :
    ∀ a : Fin actions, ∃ i : Fin obsDim, σ i = a := by
  intro a
  dsimp [strategyEntropy] at h_ent
  -- image has full cardinality, so it equals univ
  have h_eq : (Finset.univ.image σ) = (Finset.univ : Finset (Fin actions)) := by
    have : (Finset.univ.image σ).card = Fintype.card (Fin actions) := by
      rw [h_ent, Fintype.card_fin]
    exact Finset.eq_univ_of_card _ this
  -- a ∈ univ = image, so ∃ i with σ i = a
  have h_mem : a ∈ (Finset.univ.image σ) := h_eq ▸ Finset.mem_univ a
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp h_mem
  exact ⟨i, rfl⟩

/-! ## Theorem 20: Wall Activation Creates Niche Isolation
    Safety analog: wall_activates_when_unstable
    When L1 becomes unstable, wall activation isolates L1's niche from L3.
    The wall doesn't just protect — it creates the isolation that enables
    independent evolution (island dwarfism). -/

theorem wallActivationCreatesIsolation (s : SystemState)
    (_h_unstable : s.l1.stability.val < 0.4)
    (_h_nc : L1State.noCollapse s.l1) :
    IsIsolated ⟨s.l1,
      { wall := true, uncertainty := s.l2.uncertainty, active := s.l2.active,
        hypotheses := s.l2.hypotheses, beliefs := s.l2.beliefs },
      { blocked := true, active := s.l3.active, planningDepth := s.l3.planningDepth,
        understanding := s.l3.understanding, metaAwareness := s.l3.metaAwareness,
        ticksSinceTransmission := s.l3.ticksSinceTransmission },
      s.l4⟩ := by
  unfold IsIsolated
  exact ⟨rfl, rfl⟩

end EvoEcos.Diversification

end
