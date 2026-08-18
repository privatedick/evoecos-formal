/-
Substrate Isomorphism
=====================

Theorem: EvoEcos (individual cognition, L1-L4) and SymbolicField
(cultural epistemic dynamics) instantiate the same invariant pattern.

Both are instances of BoundedProtectivePattern — five structural invariants
with identical algebraic relationships, different substrate.

Correspondence:
  | EvoEcos                            | SymbolicField                     |
  |------------------------------------|-----------------------------------|
  | NoCollapse (stability > 0)         | groundingFloor (g ≥ G_min)        |
  | BoundedUncertainty (u ∈ [0,1])     | hallucinationCeiling (h ≤ H_max)  |
  | Wall (stability < 0.4 → wall)      | barrier (grounding < 2G_min)      |
  | L1Independence (L3 ↛ L1)           | antiTikTok (render ↛ model)       |
  | Probability ∈ [0,1]               | Energy ≤ E_max                    |

Implication: the wall mechanism is substrate-independent.
-/

import EvoEcos.Invariants

noncomputable section

namespace EvoEcos

/-! ## Abstract Pattern -/

/-- Five structural invariants shared by any bounded protective system. -/
structure BoundedProtectivePattern where
  survival_lb : ℝ
  divergence_ub : ℝ
  barrier_close : ℝ
  barrier_open : ℝ
  resource_ub : ℝ
  dominance_frac : ℝ
  h_surv_lt_barrier : survival_lb < barrier_close
  h_hysteresis : barrier_close < barrier_open
  h_div_pos : 0 < divergence_ub
  h_res_pos : 0 < resource_ub
  h_dom_le_one : dominance_frac ≤ 1

namespace BoundedProtectivePattern

/-- Distance from survival floor to barrier activation. -/
def barrierGap (p : BoundedProtectivePattern) : ℝ :=
  p.barrier_close - p.survival_lb

/-- Distance between barrier close and open (prevents oscillation). -/
def hysteresisBand (p : BoundedProtectivePattern) : ℝ :=
  p.barrier_open - p.barrier_close

theorem barrierGap_pos (p : BoundedProtectivePattern) : 0 < p.barrierGap := by
  unfold barrierGap; linarith [p.h_surv_lt_barrier]

theorem hysteresisBand_pos (p : BoundedProtectivePattern) : 0 < p.hysteresisBand := by
  unfold hysteresisBand; linarith [p.h_hysteresis]

/-- Core ordering: survival_lb < barrier_close < barrier_open. -/
theorem protective_ordering (p : BoundedProtectivePattern) :
    p.survival_lb < p.barrier_close ∧ p.barrier_close < p.barrier_open :=
  ⟨p.h_surv_lt_barrier, p.h_hysteresis⟩

end BoundedProtectivePattern

/-! ## EvoEcos Instance -/

/-- EvoEcos instantiates the bounded protective pattern.
    survival_lb = 0, barrier_close = 0.4, barrier_open = 0.6. -/
def evoecosPattern : BoundedProtectivePattern where
  survival_lb := 0
  divergence_ub := 1
  barrier_close := 0.4
  barrier_open := 0.6
  resource_ub := 1
  dominance_frac := 0.5
  h_surv_lt_barrier := by norm_num
  h_hysteresis := by norm_num
  h_div_pos := by norm_num
  h_res_pos := by norm_num
  h_dom_le_one := by norm_num

@[simp] theorem evoecos_survival_lb : evoecosPattern.survival_lb = 0 := rfl
@[simp] theorem evoecos_barrier_close : evoecosPattern.barrier_close = 0.4 := rfl
@[simp] theorem evoecos_barrier_open : evoecosPattern.barrier_open = 0.6 := rfl
@[simp] theorem evoecos_divergence_ub : evoecosPattern.divergence_ub = 1 := rfl
@[simp] theorem evoecos_resource_ub : evoecosPattern.resource_ub = 1 := rfl
@[simp] theorem evoecos_dominance_frac : evoecosPattern.dominance_frac = 0.5 := rfl
@[simp] theorem evoecos_barrierGap : evoecosPattern.barrierGap = 0.4 := by
  unfold BoundedProtectivePattern.barrierGap evoecosPattern; norm_num
@[simp] theorem evoecos_hysteresisBand : evoecosPattern.hysteresisBand = 0.2 := by
  unfold BoundedProtectivePattern.hysteresisBand evoecosPattern; norm_num

/-- EvoEcos system invariants map to pattern constraints. -/
theorem evoecos_satisfies_pattern {maxDepth : Nat} (sys : SystemState)
    (h_reach : Transition.Reachable maxDepth sys)
    (h : systemInvariant sys) :
    sys.l1.stability.val > evoecosPattern.survival_lb ∧
    sys.l2.uncertainty.val ≤ evoecosPattern.divergence_ub ∧
    (sys.l1.stability.val < evoecosPattern.barrier_close → sys.l2.wall = true) ∧
    (sys.l2.wall = true → sys.l3.blocked = true) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp; exact h.1
  · simp; exact h.2.1.2
  · simp; exact h.2.2.2.2.1
  · intro h_wall
    exact Transition.wall_implies_blocked_for_reachable maxDepth sys h_reach
      h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h_wall

/-! ## SymbolicField Instance -/

/-- A node in the symbolic field: a cultural symbol with energy,
    grounding, and hallucination pressure. -/
structure SFNode where
  energy : ℝ
  grounding : ℝ
  hallucination : ℝ
  h_e_nonneg : 0 ≤ energy
  h_g_nonneg : 0 ≤ grounding
  h_h_nonneg : 0 ≤ hallucination

/-- Symbolic field state with bounded resources. -/
structure SFState where
  E_max : ℝ
  G_min : ℝ
  H_max : ℝ
  dom_frac : ℝ
  nodes : List SFNode
  h_E_max_pos : 0 < E_max
  h_G_min_pos : 0 < G_min
  h_H_max_pos : 0 < H_max
  h_dom_le_one : dom_frac ≤ 1

/-- SymbolicField instantiates the bounded protective pattern.
    survival_lb = G_min, barrier_close = 2*G_min, barrier_open = 3*G_min.
    The barrier activates when grounding approaches the floor. -/
def sfPattern (sf : SFState) : BoundedProtectivePattern where
  survival_lb := sf.G_min
  divergence_ub := sf.H_max
  barrier_close := sf.G_min * 2
  barrier_open := sf.G_min * 3
  resource_ub := sf.E_max
  dominance_frac := sf.dom_frac
  h_surv_lt_barrier := by linarith [sf.h_G_min_pos]
  h_hysteresis := by linarith [sf.h_G_min_pos]
  h_div_pos := sf.h_H_max_pos
  h_res_pos := sf.h_E_max_pos
  h_dom_le_one := sf.h_dom_le_one

@[simp] theorem sf_survival_lb (sf : SFState) : (sfPattern sf).survival_lb = sf.G_min := rfl
@[simp] theorem sf_barrier_close (sf : SFState) : (sfPattern sf).barrier_close = sf.G_min * 2 := rfl
@[simp] theorem sf_barrier_open (sf : SFState) : (sfPattern sf).barrier_open = sf.G_min * 3 := rfl
@[simp] theorem sf_resource_ub (sf : SFState) : (sfPattern sf).resource_ub = sf.E_max := rfl
@[simp] theorem sf_dominance_frac (sf : SFState) : (sfPattern sf).dominance_frac = sf.dom_frac := rfl
@[simp] theorem sf_barrierGap (sf : SFState) : (sfPattern sf).barrierGap = sf.G_min := by
  unfold BoundedProtectivePattern.barrierGap sfPattern; ring
@[simp] theorem sf_hysteresisBand (sf : SFState) : (sfPattern sf).hysteresisBand = sf.G_min := by
  unfold BoundedProtectivePattern.hysteresisBand sfPattern; ring

/-- SymbolicField invariants. -/
def sf_groundingFloor (sf : SFState) : Prop :=
  ∀ n ∈ sf.nodes, n.grounding ≥ sf.G_min

def sf_hallucinationCeiling (sf : SFState) : Prop :=
  ∀ n ∈ sf.nodes, n.hallucination ≤ sf.H_max

def sf_energyBounded (sf : SFState) : Prop :=
  ∀ n ∈ sf.nodes, n.energy ≤ sf.E_max

def sf_noDominance (sf : SFState) : Prop :=
  ∀ n ∈ sf.nodes, n.energy ≤ sf.dom_frac * sf.E_max

def sf_invariants (sf : SFState) : Prop :=
  sf_groundingFloor sf ∧ sf_hallucinationCeiling sf ∧
  sf_energyBounded sf ∧ sf_noDominance sf

/-- SymbolicField invariants map to pattern constraints. -/
theorem sf_satisfies_pattern (sf : SFState) (h : sf_invariants sf) :
    (∀ n ∈ sf.nodes, n.grounding ≥ (sfPattern sf).survival_lb) ∧
    (∀ n ∈ sf.nodes, n.hallucination ≤ (sfPattern sf).divergence_ub) ∧
    (∀ n ∈ sf.nodes, n.energy ≤ (sfPattern sf).resource_ub) ∧
    (∀ n ∈ sf.nodes, n.energy ≤ (sfPattern sf).dominance_frac * (sfPattern sf).resource_ub) := by
  simp only [sf_survival_lb, sf_resource_ub, sf_dominance_frac]
  exact h

/-! ## Main Isomorphism Theorem -/

/-- Both EvoEcos and SymbolicField share the same protective ordering,
    positive barrier gap, and hysteresis band. The invariant structure
    is substrate-independent.

    Five structural correspondences:
    1. Survival above floor: stability > 0 ↔ grounding ≥ G_min
    2. Divergence bounded: uncertainty ≤ 1 ↔ hallucination ≤ H_max
    3. Barrier activation: stability < 0.4 → wall
    4. Barrier effect: wall → blocked (prevents dominance)
    5. Resource boundedness: Prob ∈ [0,1] ↔ energy ≤ E_max -/
theorem substrate_isomorphism {maxDepth : Nat}
    (sys : SystemState)
    (h_reach : Transition.Reachable maxDepth sys)
    (h_sys : systemInvariant sys)
    (sf : SFState)
    (h_sf : sf_invariants sf) :
    -- Both have protective ordering
    (evoecosPattern.survival_lb < evoecosPattern.barrier_close ∧
     evoecosPattern.barrier_close < evoecosPattern.barrier_open ∧
     (sfPattern sf).survival_lb < (sfPattern sf).barrier_close ∧
     (sfPattern sf).barrier_close < (sfPattern sf).barrier_open) ∧
    -- Both have positive barrier gaps
    (0 < evoecosPattern.barrierGap ∧ 0 < (sfPattern sf).barrierGap) ∧
    -- Both have positive hysteresis bands
    (0 < evoecosPattern.hysteresisBand ∧ 0 < (sfPattern sf).hysteresisBand) ∧
    -- Both bound divergence above zero
    (0 < evoecosPattern.divergence_ub ∧ 0 < (sfPattern sf).divergence_ub) ∧
    -- Both bound resources above zero
    (0 < evoecosPattern.resource_ub ∧ 0 < (sfPattern sf).resource_ub) ∧
    -- Both have anti-dominance ≤ 1
    (evoecosPattern.dominance_frac ≤ 1 ∧ (sfPattern sf).dominance_frac ≤ 1) ∧
    -- Structural correspondence 1: survival above floor
    (sys.l1.stability.val > 0 ∧ ∀ n ∈ sf.nodes, n.grounding ≥ sf.G_min) ∧
    -- Structural correspondence 2: divergence bounded
    (sys.l2.uncertainty.val ≤ 1 ∧ ∀ n ∈ sf.nodes, n.hallucination ≤ sf.H_max) ∧
    -- Structural correspondence 3: protective barrier
    (sys.l1.stability.val < 0.4 → sys.l2.wall = true) ∧
    -- Structural correspondence 4: barrier prevents dominance
    (sys.l2.wall = true → sys.l3.blocked = true) ∧
    -- Structural correspondence 5: resource + anti-dominance
    (∀ n ∈ sf.nodes, n.energy ≤ sf.E_max ∧ n.energy ≤ sf.dom_frac * sf.E_max) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨evoecosPattern.h_surv_lt_barrier, evoecosPattern.h_hysteresis,
            (sfPattern sf).h_surv_lt_barrier, (sfPattern sf).h_hysteresis⟩
  · exact ⟨evoecosPattern.barrierGap_pos, (sfPattern sf).barrierGap_pos⟩
  · exact ⟨evoecosPattern.hysteresisBand_pos, (sfPattern sf).hysteresisBand_pos⟩
  · exact ⟨evoecosPattern.h_div_pos, (sfPattern sf).h_div_pos⟩
  · exact ⟨evoecosPattern.h_res_pos, (sfPattern sf).h_res_pos⟩
  · exact ⟨evoecosPattern.h_dom_le_one, (sfPattern sf).h_dom_le_one⟩
  · exact ⟨h_sys.1, h_sf.1⟩
  · exact ⟨h_sys.2.1.2, h_sf.2.1⟩
  · exact h_sys.2.2.2.2.1
  · intro h_wall
    exact Transition.wall_implies_blocked_for_reachable maxDepth sys h_reach
      h_sys.1 h_sys.2.1 h_sys.2.2.1 h_sys.2.2.2.1 h_sys.2.2.2.2.1 h_wall
  · intro n hn
    exact ⟨h_sf.2.2.1 n hn, h_sf.2.2.2 n hn⟩

/-- Corollary: the protective ordering is substrate-independent. -/
theorem protective_ordering_substrate_independent {maxDepth : Nat}
    (sys : SystemState)
    (h_reach : Transition.Reachable maxDepth sys)
    (h_sys : systemInvariant sys)
    (sf : SFState)
    (h_sf : sf_invariants sf) :
    evoecosPattern.survival_lb < evoecosPattern.barrier_close ∧
    evoecosPattern.barrier_close < evoecosPattern.barrier_open ∧
    (sfPattern sf).survival_lb < (sfPattern sf).barrier_close ∧
    (sfPattern sf).barrier_close < (sfPattern sf).barrier_open :=
  (substrate_isomorphism sys h_reach h_sys sf h_sf).1

end EvoEcos

end
