/-
# Resource Gap Theory
## Extending EvoEcos with Resource Constraints

**Author:** Security Audit Team
**Date:** 2026-04-12
**Purpose:** Formalize resource constraints in cognitive architecture

### Key Concepts

1. **Cognitive Gap**: I_exist (predicted) vs I_exploit (actual) - STRUCTURAL
2. **Resource Gap**: Modeled state vs available RAM/CPU - PHYSICAL
3. **Interaction**: High cognitive load → different resource strategy
4. **Invariant**: History must fit in available memory

### Motivation

The security audit revealed unbounded list growth:
- `consequence_history` in responsible.py
- `environment_history` in meta_learning_layer.py

TLA+ proofs assume finite state spaces, but Python lists are unbounded.
This creates a gap between:
- **Theoretical model** (finite state, verified)
- **Physical implementation** (unbounded resources, vulnerable)
-/

import EvoEcos.Layers
import EvoEcos.Invariants
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Basic

namespace EvoEcos

/-! ## Resource State -/

/-- Available physical resources -/
structure ResourceState where
  availableMemory : Nat  -- bytes
  availableCPU : Nat      -- percent (0-100)
  historySize : Nat       -- current size of history buffers
  deriving Repr

namespace ResourceState
  /-- Initial resource state (generous assumption) -/
  def init : ResourceState :=
    {
      availableMemory := 1000000000,  -- 1GB
      availableCPU := 100,
      historySize := 0
    }

  /-- Check if system is under resource pressure -/
  def isUnderPressure (threshold : Nat) : Prop :=
    availableMemory < threshold
end ResourceState


/-! ## Resource Constraints -/

/-- Configuration for resource-aware behavior -/
structure ResourceConstraints where
  maxHistory : Nat       -- Maximum history when resources plentiful
  compactHistory : Nat   -- Smaller limit when resources low
  memoryThreshold : Nat  -- When to switch to compact mode (bytes)
  hcompact : compactHistory ≤ maxHistory
  deriving Repr

/-- Default resource constraints -/
def defaultConstraints : ResourceConstraints :=
  {
    maxHistory := 10000,
    compactHistory := 1000,
    memoryThreshold := 200000000,  -- 200MB
    hcompact := by norm_num
  }


/-! ## Resource Gap Invariants -/

/-- Primary invariant: History fits in available memory -/
def resourceGapInvariant (rs : ResourceState) (rc : ResourceConstraints) : Prop :=
  (rs.availableMemory ≥ rc.memoryThreshold ∧ rs.historySize ≤ rc.maxHistory) ∨
  (rs.availableMemory < rc.memoryThreshold ∧ rs.historySize ≤ rc.compactHistory)


/-! ## Resource Gap Theorems -/

/-- When memory is low, history MUST be compact -/
theorem compact_history_when_low_memory
    {rs : ResourceState}
    {rc : ResourceConstraints}
    (h : rs.availableMemory < rc.memoryThreshold) :
    resourceGapInvariant rs rc → rs.historySize ≤ rc.compactHistory := by
  intro hinv
  -- The invariant is a disjunction:
  -- (mem ≥ threshold ∧ size ≤ max) ∨ (mem < threshold ∧ size ≤ compact)
  -- Since mem < threshold, the left disjunct is impossible (contradiction with h)
  -- so the right disjunct must hold, giving size ≤ compact
  cases' hinv with hleft hright
  · -- Left case: availableMemory ≥ threshold ∧ historySize ≤ maxHistory
    -- But h says availableMemory < threshold — contradiction
    linarith
  · -- Right case: availableMemory < threshold ∧ historySize ≤ compactHistory
    exact hright.2


/-- Adding to history preserves invariant if we respect bounds.
    For the high-memory branch, h_within suffices. For the low-memory
    branch, we also need the addition to stay within compactHistory. -/
theorem history_addition_preserves_invariant
    {rs : ResourceState}
    {rc : ResourceConstraints}
    (addition : Nat)
    (h_before : resourceGapInvariant rs rc)
    (h_within : rs.historySize + addition ≤ rc.maxHistory)
    (h_compact : rs.historySize + addition ≤ rc.compactHistory) :
    let rs' := { rs with historySize := rs.historySize + addition }
    resourceGapInvariant rs' rc := by
  simp only [resourceGapInvariant]
  cases' h_before with hleft hright
  · left; exact ⟨hleft.1, h_within⟩
  · right; exact ⟨hright.1, h_compact⟩


/-- Compacting history restores invariant -/
theorem compacting_restores_invariant
    {rs : ResourceState}
    {rc : ResourceConstraints}
    (h : rs.historySize > rc.compactHistory) :
    let rs' := { rs with historySize := rc.compactHistory }
    resourceGapInvariant rs' rc := by
  -- After compacting, historySize = compactHistory.
  -- Both branches of the disjunction can be satisfied:
  -- Left:  compactHistory ≤ maxHistory (from hcompact)
  -- Right: compactHistory ≤ compactHistory (trivially)
  -- Pick based on memory state
  show resourceGapInvariant { rs with historySize := rc.compactHistory } rc
  simp only [resourceGapInvariant]
  by_cases hmem : rs.availableMemory < rc.memoryThreshold
  · right; exact ⟨hmem, le_refl _⟩
  · left; exact ⟨by linarith, rc.hcompact⟩


/-! ## Bounded History Theorem (Episode-Length Bound) -/

/-- Per-step contribution to history (one state snapshot per step) -/
def stateSize : Nat := 1

/-- After `steps` execution steps, history size is at most `steps * stateSize`.
    Since `stateSize = 1`, this simplifies to `historySize ≤ steps`. -/
theorem historySize_bounded (steps : Nat) (currentHistory : Nat)
    (h_current : currentHistory ≤ steps) :
    currentHistory ≤ steps * stateSize := by
  unfold stateSize
  rw [Nat.mul_one]
  exact h_current

/-- After `steps` execution steps, history size never exceeds `maxSteps * stateSize`.
    This holds because each step adds at most `stateSize` entries. -/
theorem historySize_bounded_by_maxSteps (maxSteps steps : Nat) (currentHistory : Nat)
    (h_steps : steps ≤ maxSteps)
    (h_history : currentHistory ≤ steps) :
    currentHistory ≤ maxSteps * stateSize := by
  -- Chain: currentHistory ≤ steps ≤ maxSteps ≤ maxSteps * stateSize (since stateSize = 1)
  have h_bound := historySize_bounded steps currentHistory h_history
  unfold stateSize at h_bound
  rw [Nat.mul_one] at h_bound
  unfold stateSize
  rw [Nat.mul_one]
  exact Nat.le_trans h_bound h_steps

/-- Bounded episode with high-memory assumption satisfies resource invariant.
    When memory is sufficient (≥ threshold), any history ≤ maxSteps ≤ maxHistory
    satisfies the high-memory branch of the invariant. -/
theorem bounded_episode_high_memory
    (maxSteps : Nat)
    (rc : ResourceConstraints)
    (h_reasonable : maxSteps ≤ rc.maxHistory)
    (currentHistory : Nat)
    (h_history : currentHistory ≤ maxSteps)
    (mem cpu : Nat)
    (h_mem : mem ≥ rc.memoryThreshold) :
    resourceGapInvariant { availableMemory := mem, availableCPU := cpu, historySize := currentHistory } rc := by
  simp only [resourceGapInvariant]
  left
  exact ⟨h_mem, Nat.le_trans h_history h_reasonable⟩

/-- Bounded episode with compact-friendly maxSteps satisfies resource invariant in both branches.
    This is the main bounded-history theorem: if maxSteps ≤ compactHistory,
    then regardless of memory level, the resource gap invariant holds because
    currentHistory ≤ maxSteps ≤ compactHistory ≤ maxHistory. -/
theorem bounded_episode_both_branches
    (maxSteps : Nat)
    (rc : ResourceConstraints)
    (h_compact : maxSteps ≤ rc.compactHistory)
    (currentHistory : Nat)
    (h_history : currentHistory ≤ maxSteps) :
    ∀ (mem cpu : Nat),
      resourceGapInvariant { availableMemory := mem, availableCPU := cpu, historySize := currentHistory } rc := by
  intro mem cpu
  simp only [resourceGapInvariant]
  by_cases h_mem : mem < rc.memoryThreshold
  · -- Low memory (< threshold): historySize ≤ compactHistory
    right
    exact ⟨h_mem, Nat.le_trans h_history h_compact⟩
  · -- High memory (≥ threshold): historySize ≤ compactHistory ≤ maxHistory
    left
    exact ⟨not_lt.mp h_mem, Nat.le_trans (Nat.le_trans h_history h_compact) rc.hcompact⟩

/-! ## NoCollapse Under Resource Constraints -/

/-- Resource-aware system state: extends SystemState with resource tracking -/
structure ResourceAwareSystemState where
  sys : EvoEcos.SystemState
  res : ResourceState

namespace ResourceAwareSystemState

/-- Initial resource-aware state -/
noncomputable def init (maxDepth : Nat) : ResourceAwareSystemState :=
  {
    sys := EvoEcos.SystemState.init maxDepth
    res := ResourceState.init
  }

/-- Resource-aware system invariant: system invariant AND resource gap invariant -/
def resourceAwareInvariant (s : ResourceAwareSystemState) (rc : ResourceConstraints) : Prop :=
  EvoEcos.systemInvariant s.sys ∧
  resourceGapInvariant s.res rc

end ResourceAwareSystemState

/-- NoCollapse holds under resource constraints.
    The resource gap invariant constrains history size but does NOT affect
    L1 stability. L1 operates independently (L1Independence invariant),
    so resource pressure cannot cause collapse. -/
theorem noCollapse_with_resources
    (maxDepth : Nat)
    (s : ResourceAwareSystemState)
    (rc : ResourceConstraints)
    (h_inv : ResourceAwareSystemState.resourceAwareInvariant s rc) :
    EvoEcos.L1State.noCollapse s.sys.l1 := by
  -- NoCollapse follows from the system invariant component,
  -- which is independent of resource constraints.
  exact h_inv.1.1

/-- Resource-aware initial state satisfies the combined invariant.
    Initial historySize = 0 satisfies both branches trivially. -/
theorem resourceAware_invariant_init
    (maxDepth : Nat)
    (rc : ResourceConstraints) :
    ResourceAwareSystemState.resourceAwareInvariant
      (ResourceAwareSystemState.init maxDepth) rc := by
  constructor
  · -- System invariant: follows from systemInvariant_init
    exact EvoEcos.systemInvariant_init maxDepth
  · -- Resource gap invariant: initial historySize = 0 ≤ anything
    -- Both branches require historySize ≤ maxHistory or ≤ compactHistory,
    -- and 0 ≤ n for all n, so pick based on memory state.
    simp only [ResourceAwareSystemState.init, resourceGapInvariant, ResourceState.init]
    by_cases h_mem : (1000000000 : Nat) < rc.memoryThreshold
    · right; exact ⟨h_mem, Nat.zero_le _⟩
    · left; exact ⟨not_lt.mp h_mem, Nat.zero_le _⟩

/-!
## Application to EvoEcos

### Component Applications:

1. **ResponsibleAgent.consequence_history**
   - Must obey resourceGapInvariant
   - Use ResourceAwareHistory from security_fixes.py
   - Compact to 1000 entries when RAM < threshold

2. **MetaLearningLayer.environment_history**
   - Must obey resourceGapInvariant
   - Use ResourceAwareHistory from security_fixes.py
   - Compact to 1000 entries when RAM < threshold

### Theoretical Impact:

This extends EvoEcos theory with:
- **Resource Gap**: Bridge between cognitive and physical layers
- **Adaptive Strategy**: Change behavior based on available resources
- **Formal Bounds**: Prove system respects resource constraints
- **Bounded History**: Episode length bounds history size (historySize ≤ maxSteps)
- **NoCollapse Under Resources**: L1 independence survives resource pressure

### Connection to I_exist/I_exploit:

The cognitive gap (I_exist vs I_exploit) is STRUCTURAL - it cannot be eliminated.
The resource gap is PHYSICAL - it CAN be managed.

Key insight: High cognitive load (many hypotheses) increases history size,
which increases resource pressure. This creates an INTERACTION:

```
High cognitive load → Large history → Resource pressure → Compact history → Reduced cognitive capacity
```

This is a NEW feedback loop not in original theory.

-/
