/-
EvoEcos Architecture Module
===========================

High-level architecture proofs for the three-layer cognitive system.

Key Architectural Invariants:
1. L3 can NEVER directly reach L1 - must go through L2
2. L1 operates independently of L3
3. L2 wall protects L1 when unstable
4. Graceful degradation maintains function
-/

import EvoEcos.Layers
import EvoEcos.Invariants
import InfoTheory.InfoTheory
import Thresholds.Thresholds

noncomputable section

namespace EvoEcos.Architecture

/-! ## Layer Communication Architecture -/

/-- Valid communication paths between layers -/
inductive CommPath where
  | L1_to_L2 : CommPath
  | L2_to_L1 : CommPath
  | L2_to_L3 : CommPath
  | L3_to_L2 : CommPath
deriving DecidableEq

/-- Forbidden communication paths -/
inductive ForbiddenPath where
  | L1_to_L3 : ForbiddenPath
  | L3_to_L1 : ForbiddenPath

/-! ## Architectural Invariants -/

/-- L1 independence invariant: L1 can always respond without L3 -/
structure L1Independence where
  canReflex : Bool
  canHeuristic : Bool
  l3_blocked : Bool

/-- L1 independence is maintained -/
def l1Independent (ind : L1Independence) : Prop :=
  ind.canReflex ∨ ind.canHeuristic ∨ ind.l3_blocked

/-- Initial independence state -/
def initialIndependence : L1Independence where
  canReflex := true
  canHeuristic := true
  l3_blocked := false

/-- Initial state satisfies independence -/
theorem initial_independence : l1Independent initialIndependence := by
  simp only [l1Independent, initialIndependence]
  left; trivial

/-! ## Wall Protection -/

/-- Wall state for protecting layers -/
structure WallState where
  l1_protected : Bool  -- L2→L1 bridge blocked
  l2_protected : Bool  -- L3→L2 bridge blocked
  trigger : String     -- Why wall is active

/-- Wall state invariant -/
def wallInvariant (ws : WallState) (l1Stability : Probability) : Prop :=
  l1Stability.val < Thresholds.L1_STABILITY_THRESHOLD → ws.l2_protected

/-! ## Graceful Degradation Architecture -/

/-- Degradation state machine -/
inductive DegradationMode where
  | full : DegradationMode        -- All layers active
  | reduced : DegradationMode     -- L3 blocked, L2 reduced
  | minimal : DegradationMode     -- Only L1 active
  | survival : DegradationMode    -- L1 in survival mode
deriving DecidableEq

/-! ## Meta-Awareness Architecture -/

/-- Meta-awareness state -/
structure MetaAwareness where
  level : Probability
  validated : Bool  -- Is dependency on understanding validated?
  self_monitoring : Bool

/-- Meta-awareness invariant -/
def metaAwarenessInvariant (ma : MetaAwareness) : Prop :=
  ma.level.val > 0.5 → ma.validated ∧ ma.self_monitoring

/-- Validated dependency enables safe understanding -/
theorem validated_dependency_safe (ma : MetaAwareness)
    (h : ma.level.val > 0.5) (hinv : metaAwarenessInvariant ma) :
    ma.validated ∧ ma.self_monitoring := by
  exact hinv h

/-! ## Architecture Invariant -/

/-- Combined architectural invariant -/
structure ArchitectureInvariant where
  l1_independent : L1Independence
  wall_state : WallState
  degradation : DegradationMode
  meta_awareness : MetaAwareness

/-- All architectural invariants hold -/
def allArchitectureInvariants (ai : ArchitectureInvariant)
    (s : SystemState) : Prop :=
  l1Independent ai.l1_independent ∧
  wallInvariant ai.wall_state s.l1.stability ∧
  (s.l1.stability.val < Thresholds.L1_STABILITY_THRESHOLD → s.l2.wall) ∧
  metaAwarenessInvariant ai.meta_awareness

/-- Architecture invariant theorem: blocked L3 cannot plan -/
theorem architecture_sound_blocking (s : SystemState)
    (hblocked : s.l3.blocked = true) :
    ¬L3State.canPlan s.l3 s.l2 :=
  blocked_implies_cannot_plan s.l3 s.l2 hblocked

/-- Architecture invariant theorem: wall activates when L1 unstable -/
theorem architecture_sound_wall (l1 : L1State) (l2 : L2State)
    (h : l1.stability.val < 0.4) :
    (L2State.activateWall l2 l1).wall = true :=
  wall_activates_when_unstable l1 l2 h

end EvoEcos.Architecture

end
