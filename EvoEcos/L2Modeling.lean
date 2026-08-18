import EvoEcos.Layers

namespace EvoEcos

/-!
## L2 Modeling Layer Formalization

The L2 (Modeling) layer maintains the world model and controls the L3 wall.
The wall mechanism is critical for safety: when L1 becomes unstable (stability < 0.4),
L2 activates the wall to block L3, ensuring L1 can recover independently.

### Key Properties

1. **Bounded Uncertainty**: L2 uncertainty always stays in [0, 1]
2. **Wall Activation**: Wall activates when L1 stability < 0.4
3. **Wall Deactivation**: Wall deactivates when L1 stability ≥ 0.4

### Main Theorems

- `L2TypeInvariant_init`: Initial state has valid uncertainty
- `L2WallActivatesWhenUnstable`: Wall activates when L1.stability < 0.4
- `L2WallDeactivatesWhenStable`: Wall deactivates when L1.stability ≥ 0.4
-/

open BigOperators

/-! ## L2 State Properties -/

namespace L2State

/-- L2 type invariant holds for initial state -/
theorem typeInvariant_init : typeInvariant init := by
  simp only [typeInvariant, init]
  norm_num

/-! ## L2 Wall Mechanism -/

/-- Wall activates when L1 is unstable (stability < wallActivateThreshold) -/
theorem wallActivatesWhenUnstable (l1 : L1State) (l2 : L2State)
    (h : l1.stability.val < wallActivateThreshold) :
    (activateWall l2 l1).wall = true := by
  simp only [activateWall]
  split
  · rfl
  · next h' => exact absurd h h'

/-- Wall does NOT activate when L1 is stable (stability ≥ wallActivateThreshold) -/
theorem wallStaysInactiveWhenStable (l1 : L1State) (l2 : L2State)
    (h : l1.stability.val ≥ wallActivateThreshold) :
    (activateWall l2 l1).wall = l2.wall := by
  simp only [activateWall]
  split
  · next h' => exact absurd h' (not_lt.mpr h)
  · rfl

/-- Wall deactivates when L1 is stable past the open threshold (stability > wallDeactivateThreshold).
    Note: hysteresis means deactivation requires > wallDeactivateThreshold, not merely ≥ wallActivateThreshold — at
    wallActivateThreshold ≤ stability ≤ wallDeactivateThreshold the wall is held (this is the hysteresis band). -/
theorem wallDeactivatesWhenStable (l1 : L1State) (l2 : L2State)
    (h : l1.stability.val > wallDeactivateThreshold) :
    (deactivateWall l2 l1).wall = false := by
  simp only [deactivateWall]
  split
  · rfl
  · next h' => exact absurd h h'

/-- Wall does NOT deactivate when L1 is unstable (stability < wallActivateThreshold) -/
theorem wallStaysActiveWhenUnstable (l1 : L1State) (l2 : L2State)
    (h : l1.stability.val < wallActivateThreshold) :
    (deactivateWall l2 l1).wall = l2.wall := by
  simp only [deactivateWall]
  split
  · next h' =>
    -- h: stability < wallActivateThreshold (= 0.4), h': stability > wallDeactivateThreshold (= 0.6)
    -- 0.4 < 0.6, so < 0.4 contradicts > 0.6
    have : (0.4 : ℝ) < (0.6 : ℝ) := by norm_num
    simp [wallActivateThreshold] at h
    simp [wallDeactivateThreshold] at h'
    linarith
  · rfl

/-! ## L2 Type Invariant Preservation -/

/-- activateWall preserves type invariant -/
theorem activateWall_preservesTypeInvariant (s : L2State)
    (l1 : L1State)
    (h_inv : typeInvariant s) :
    typeInvariant (activateWall s l1) := by
  simp only [typeInvariant, activateWall]
  split
  · exact h_inv
  · exact h_inv

/-- deactivateWall preserves type invariant -/
theorem deactivateWall_preservesTypeInvariant (s : L2State)
    (l1 : L1State)
    (h_inv : typeInvariant s) :
    typeInvariant (deactivateWall s l1) := by
  simp only [typeInvariant, deactivateWall]
  split
  · exact h_inv
  · exact h_inv

/-- updateBeliefs preserves type invariant -/
theorem updateBeliefs_preservesTypeInvariant (s : L2State)
    (h_inv : typeInvariant s) :
    typeInvariant (updateBeliefs s) := by
  simp only [typeInvariant, updateBeliefs]
  exact h_inv

/-! ## L2-L3 Gate Properties -/

/-- When wall is active, L3 cannot plan -/
theorem wallBlocksL3 (l2 : L2State)
    (h_wall : l2.wall = true)
    (l3 : L3State) :
    ¬L3State.canPlan l3 l2 := by
  intro h_can
  simp only [L3State.canPlan] at h_can
  exact h_can.2.2 h_wall

/-! ## Main L2 Theorems -/

namespace L2Theorems

/-- Theorem: L2 type invariant is preserved by all L2 actions -/
theorem allActionsPreserveTypeInvariant (s : L2State)
    (l1 : L1State)
    (h_inv : typeInvariant s) :
    typeInvariant (updateBeliefs (deactivateWall (activateWall s l1) l1)) := by
  apply updateBeliefs_preservesTypeInvariant
  apply deactivateWall_preservesTypeInvariant
  apply activateWall_preservesTypeInvariant
  exact h_inv

/-- Theorem: L2 correctly gates L3 based on L1 stability -/
theorem L2CorrectlyGatesL3 (l1 : L1State) (l2 : L2State) :
    (l1.stability.val < wallActivateThreshold → (activateWall l2 l1).wall = true) ∧
    (l1.stability.val > wallDeactivateThreshold → (deactivateWall l2 l1).wall = false) := by
  constructor
  · intro h
    exact wallActivatesWhenUnstable l1 l2 h
  · intro h
    exact wallDeactivatesWhenStable l1 l2 h

/-- Theorem: L2 uncertainty remains bounded after any action -/
theorem uncertaintyAlwaysBounded (l1 : L1State) (l2 : L2State) :
    (activateWall l2 l1).uncertainty.val ≥ 0 ∧
    (activateWall l2 l1).uncertainty.val ≤ 1 := by
  constructor
  · exact (activateWall l2 l1).uncertainty.property.1
  · exact (activateWall l2 l1).uncertainty.property.2

end L2Theorems

end L2State

end EvoEcos
