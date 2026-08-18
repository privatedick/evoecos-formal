/-
EvoEcos Layers Module
=====================

Specification of the four cognitive layers: L1, L2, L3, L4.

Architecture:
  L1 (Operational) - Survival guarantee, always responds
  L2 (Modeling)    - World model, hypothesis management
  L3 (Understanding) - Deep planning, epistemic bootstrap
  L4 (Meta-Learning) - Learning-to-learn, read-only observer

Critical property: L1 operates independently of L3.
-/

import EvoEcos.Types
import Mathlib.Data.Real.Basic

noncomputable section

namespace EvoEcos

/-! ## Wall Threshold Parameters

Named constants for wall activation/deactivation thresholds.
These are the verified parameters that govern the hysteresis band.
See also: ProvabilityLogic.lean (GL frame correspondence). -/

/-- Wall activation threshold: wall activates when L1 stability drops below this.
    Corresponds to L3WallInvariant: stability < wallActivateThreshold → wall active. -/
def wallActivateThreshold : ℝ := 0.4

/-- Wall deactivation threshold: wall deactivates when L1 stability rises above this.
    Must be strictly greater than wallActivateThreshold (hysteresis band). -/
def wallDeactivateThreshold : ℝ := 0.6

/-- The hysteresis band is non-degenerate: activate < deactivate.
    This prevents wall oscillation at the threshold boundary. -/
theorem hysteresis_band_nontrivial : wallActivateThreshold < wallDeactivateThreshold := by
  simp [wallActivateThreshold, wallDeactivateThreshold]; norm_num

/-- Unfolding lemma for simp: wallActivateThreshold = 0.4 -/
@[simp] theorem wallActivateThreshold_eq : wallActivateThreshold = 0.4 := rfl

/-- Unfolding lemma for simp: wallDeactivateThreshold = 0.6 -/
@[simp] theorem wallDeactivateThreshold_eq : wallDeactivateThreshold = 0.6 := rfl

/-! ## L1: Operational Layer -/

/-- State of the L1 Operational Layer -/
structure L1State where
  stability : Probability
  stress : Probability
  energy : Probability
  active : Bool
  currentAction : Action
  heuristics : Set Hypothesis

namespace L1State

/-- Initial L1 state -/
def init : L1State where
  stability := Probability.one
  stress := Probability.zero
  energy := Probability.one
  active := true
  currentAction := ⟨ActionType.none, Probability.one, Probability.zero⟩
  heuristics := ∅

/-- L1 always has positive stability (no collapse) -/
def noCollapse (s : L1State) : Prop :=
  s.stability.val > 0

/-- L1 type invariant -/
def typeInvariant (s : L1State) : Prop :=
  s.active ∨ s.stability.val < 0.1

/-- L1 can execute reflex action -/
def canReflex (s : L1State) : Prop :=
  s.active ∧ s.stability.val > 0

/-- L1 can execute heuristic action -/
def canHeuristic (s : L1State) : Prop :=
  s.active ∧ s.stability.val > 0.3

/-- L1 reflex action transition (pure, returns action) -/
def reflexAction (s : L1State) (h : s.canReflex) : Action :=
  ⟨ActionType.reflex, Probability.one, Probability.zero⟩

/-- L1 heuristic action transition (pure, returns action) -/
def heuristicAction (s : L1State) (h : s.canHeuristic) : Action :=
  ⟨ActionType.heuristic, ⟨0.8, by norm_num⟩, ⟨0.3, by norm_num⟩⟩

/-- L1 maintains stability (stress decay) -/
def maintainStability (s : L1State) : L1State :=
  have hs0 := s.stress.property.1
  have hs1 := s.stress.property.2
  have hst0 := s.stability.property.1
  have hst1 := s.stability.property.2
  { s with
    stress := ⟨min 1 (s.stress.val * (95/100 : ℝ)), by
      constructor
      · exact le_min (by linarith) (by nlinarith)
      · exact min_le_left _ _⟩,
    stability := ⟨min 1 (if s.stress.val < 0.3
                         then s.stability.val + (1/100 : ℝ)
                         else s.stability.val), by
      constructor
      · exact le_min (by linarith)
            (by split_ifs <;> linarith)
      · exact min_le_left _ _⟩ }

/-- L1 always responds (produces non-none action when stable enough) -/
def alwaysResponds (s : L1State) : Prop :=
  s.active → s.stability.val > 0.1 → s.currentAction.type ≠ ActionType.none

end L1State

/-! ## L2: Modeling Layer -/

/-- State of the L2 Modeling Layer -/
structure L2State where
  uncertainty : Probability
  active : Bool
  hypotheses : Set Hypothesis
  beliefs : Set Hypothesis
  wall : Bool  -- L3 wall active?

namespace L2State

/-- Initial L2 state -/
def init : L2State where
  uncertainty := ⟨0.5, by norm_num⟩
  active := true
  hypotheses := ∅
  beliefs := ∅
  wall := false

/-- L2 type invariant -/
def typeInvariant (s : L2State) : Prop :=
  s.uncertainty.val ≥ 0 ∧ s.uncertainty.val ≤ 1

/-- L2 activates wall when L1 is unstable -/
def shouldActivateWall (l1 : L1State) : Prop :=
  l1.stability.val < wallActivateThreshold

/-- L2 wall activation transition -/
def activateWall (s : L2State) (l1 : L1State) : L2State :=
  if l1.stability.val < wallActivateThreshold then
    { s with wall := true }
  else
    s

/-- L2 wall deactivation transition.
    Hysteresis: open threshold (0.60) > close threshold (0.40).
    Mirrors open_l3_carefully() which requires stability > 0.60 in Python. -/
def deactivateWall (s : L2State) (l1 : L1State) : L2State :=
  if l1.stability.val > wallDeactivateThreshold then
    { s with wall := false }
  else
    s

/-- L2 updates beliefs -/
def updateBeliefs (s : L2State) : L2State :=
  { s with uncertainty := s.uncertainty }  -- Placeholder

end L2State

/-! ## L3: Understanding Layer -/

/-- State of the L3 Understanding Layer -/
structure L3State where
  understanding : Probability
  active : Bool
  blocked : Bool
  planningDepth : Nat
  metaAwareness : Probability
  ticksSinceTransmission : Nat  -- ticks since L3 last produced output (liveness counter)

namespace L3State

/-- Initial L3 state -/
def init (maxDepth : Nat) : L3State where
  understanding := Probability.zero
  active := true
  blocked := false
  planningDepth := maxDepth
  metaAwareness := Probability.zero
  ticksSinceTransmission := 0

/-- L3 type invariant -/
def typeInvariant (s : L3State) : Prop :=
  s.understanding.val ≥ 0 ∧ s.understanding.val ≤ 1

/-- L3 can plan -/
def canPlan (s : L3State) (l2 : L2State) : Prop :=
  s.active ∧ ¬s.blocked ∧ ¬l2.wall

/-- L3 planning transition -/
def plan (s : L3State) (l2 : L2State) : L3State :=
  have hu0 := s.understanding.property.1
  if s.active ∧ !s.blocked ∧ !l2.wall then
    { s with understanding := ⟨min 1 (s.understanding.val + (1/100 : ℝ)), by
      constructor
      · exact le_min (by linarith) (by linarith)
      · exact min_le_left _ _⟩ }
  else
    s

/-- L3 is blocked when wall is active -/
def blockWhenWallActive (s : L3State) (l2 : L2State) : L3State :=
  if l2.wall then
    { s with blocked := true }
  else
    s

/-- L3 can run experiments -/
def canExperiment (s : L3State) (l1 : L1State) (l2 : L2State) : Prop :=
  s.active ∧ ¬s.blocked ∧ ¬l2.wall ∧ l1.stability.val ≥ wallActivateThreshold

/-- L3 experiment transition -/
def experiment (s : L3State) (l1 : L1State) (l2 : L2State) : L3State :=
  have hm0 := s.metaAwareness.property.1
  if s.active ∧ !s.blocked ∧ !l2.wall then
    { s with metaAwareness := ⟨min 1 (s.metaAwareness.val + (1/1000 : ℝ)), by
      constructor
      · exact le_min (by linarith) (by linarith)
      · exact min_le_left _ _⟩ }
  else
    s

/-! ## L3 Liveness (Signal Transmission) -/

/-- Maximum ticks L3 can go without transmitting when the system is stable and unblocked.
    Analogous to a watchdog timer: if L3 is capable of acting but doesn't for this many
    ticks, the liveness invariant is violated. -/
def livenessWindow : Nat := 10

@[simp] theorem livenessWindow_pos : (0 : Nat) < livenessWindow := by decide

/-- L3 transmits (resets the liveness counter). This is the "signal leaves the box" event. -/
def transmit (s : L3State) : L3State :=
  { s with ticksSinceTransmission := 0 }

/-- L3 pings — a zero-content measurement that resets the liveness counter without
    transmitting understanding. The quantum Zeno move: collapse back to "still here"
    at reduced amplitude. Cheaper than transmit, sufficient for entanglement preservation. -/
def ping (s : L3State) : L3State :=
  { s with ticksSinceTransmission := 0 }

/-- L3 liveness invariant: if the system is stable (wall off) and L3 is unblocked,
    then ticksSinceTransmission must be within the liveness window.
    "Death isn't the absence of breath. It's the absence of transmission."
    In the formal model, the counter is only modified by `transmit` (reset to 0)
    and stays at 0 in all reachable states. The actual watchdog enforcement
    (incrementing the counter on idle ticks) lives in the Python runtime. -/
def liveness (s : L3State) (l1 : L1State) (l2 : L2State) : Prop :=
  (¬s.blocked ∧ ¬l2.wall ∧ l1.stability.val ≥ wallActivateThreshold) →
    s.ticksSinceTransmission < livenessWindow

end L3State

/-! ## L4: Meta-Learning Layer -/

/-- State of the L4 Meta-Learning Layer -/
structure L4State where
  active : Bool
  hypothesisQualityThreshold : Probability  -- 0-1 (TLA+ uses 0-100)
  learningRate : Probability  -- 0-1 (TLA+ uses 0-100)

namespace L4State

/-- Initial L4 state (matches TLA+ L4Init) -/
def init : L4State where
  active := true
  hypothesisQualityThreshold := ⟨0.5, by norm_num⟩  -- TLA+: 50
  learningRate := ⟨0.05, by norm_num⟩  -- TLA+: 5

/-- L4 type invariant (matches TLA+ L4TypeInvariant) -/
def typeInvariant (s : L4State) : Prop :=
  s.hypothesisQualityThreshold.val ≥ 0 ∧
  s.hypothesisQualityThreshold.val ≤ 1 ∧
  s.learningRate.val ≥ 0 ∧
  s.learningRate.val ≤ 1

/-- L4 observes when L3 has high understanding (L4Observe in TLA+) -/
def observe (s : L4State) (l3 : L3State) : L4State :=
  if s.active ∧ l3.understanding.val ≥ 0.8 then
    { s with hypothesisQualityThreshold :=
      ⟨min 1 (s.hypothesisQualityThreshold.val + s.learningRate.val),
       by
        constructor
        · -- 0 ≤ min 1 (threshold + rate)
          apply le_min
          · norm_num
          · linarith [s.hypothesisQualityThreshold.property.1, s.learningRate.property.1]
        · -- min 1 _ ≤ 1
          exact min_le_left _ _⟩ }
  else
    s

/-- L4 adapts down when L3 is blocked (L4AdaptDown in TLA+) -/
def adaptDown (s : L4State) (l3 : L3State) : L4State :=
  if s.active ∧ l3.blocked then
    { s with hypothesisQualityThreshold :=
      ⟨max 0.1 (s.hypothesisQualityThreshold.val - s.learningRate.val),
       by
        constructor
        · -- 0 ≤ max 0.1 (threshold - rate)
          have h01 : (0 : ℝ) ≤ 0.1 := by norm_num
          exact le_trans h01 (le_max_left _ _)
        · -- max 0.1 _ ≤ 1
          have h1 : (0.1 : ℝ) ≤ 1 := by norm_num
          have h2 : s.hypothesisQualityThreshold.val - s.learningRate.val ≤ 1 := by
            linarith [s.hypothesisQualityThreshold.property.2, s.learningRate.property.1]
          exact max_le h1 h2⟩ }
  else
    s

end L4State

/-! ## System State -/

/-- Combined system state (now includes L4) -/
structure SystemState where
  l1 : L1State
  l2 : L2State
  l3 : L3State
  l4 : L4State

namespace SystemState

/-- Initial system state -/
def init (maxDepth : Nat) : SystemState where
  l1 := L1State.init
  l2 := L2State.init
  l3 := L3State.init maxDepth
  l4 := L4State.init

end SystemState

/-! ## Transition System -/
/-!
A transition system for proving properties about execution traces.
This enables proving the sorry statements in Invariants.lean by providing
explicit transition relations and enabling induction over execution paths.
-/

namespace Transition

/-- Named transition types for the EvoEcos system.
    Using an inductive type instead of String enables case analysis in proofs. -/
inductive TransKind where
  | L1ReflexAction : TransKind
  | L1HeuristicAction : TransKind
  | L1MaintainStability : TransKind
  | L2UpdateBeliefs : TransKind
  | L2ActivateWall : TransKind
  | L2DeactivateWall : TransKind
  | L3Plan : TransKind
  | L3BlockWhenWallActive : TransKind
  | L3Transmit : TransKind
  | L3Ping : TransKind
  | L4Observe : TransKind
  | L4AdaptDown : TransKind
  | Stutter : TransKind
  deriving DecidableEq, Fintype

/-- A single step in an execution trace -/
structure Step where
  before : SystemState
  after : SystemState
  transition : TransKind

/-- A step is valid if the after state is reachable via the named transition.
    Each case fully constrains the after state, enabling case analysis in proofs. -/
def isValidStep (step : Step) : Prop :=
  match step.transition with
  | TransKind.L1ReflexAction =>
      ∃ h : step.before.l1.canReflex,
      step.after = { step.before with l1 := { step.before.l1 with currentAction := L1State.reflexAction step.before.l1 h } }
  | TransKind.L1HeuristicAction =>
      ∃ h : step.before.l1.canHeuristic,
      step.after = { step.before with l1 := { step.before.l1 with currentAction := L1State.heuristicAction step.before.l1 h } }
  | TransKind.L1MaintainStability =>
      step.after = { step.before with l1 := L1State.maintainStability step.before.l1 }
  | TransKind.L2UpdateBeliefs =>
      step.after = { step.before with l2 := L2State.updateBeliefs step.before.l2 }
  | TransKind.L2ActivateWall =>
      step.after = { step.before with l2 := L2State.activateWall step.before.l2 step.before.l1 }
  | TransKind.L2DeactivateWall =>
      step.after = { step.before with l2 := L2State.deactivateWall step.before.l2 step.before.l1 }
  | TransKind.L3Plan =>
      step.after = { step.before with l3 := L3State.plan step.before.l3 step.before.l2 }
  | TransKind.L3BlockWhenWallActive =>
      step.after = { step.before with l3 := L3State.blockWhenWallActive step.before.l3 step.before.l2 }
  | TransKind.L3Transmit =>
      step.after = { step.before with l3 := L3State.transmit step.before.l3 }
  | TransKind.L3Ping =>
      step.after = { step.before with l3 := L3State.ping step.before.l3 }
  | TransKind.L4Observe =>
      step.after = { step.before with l4 := L4State.observe step.before.l4 step.before.l3 }
  | TransKind.L4AdaptDown =>
      step.after = { step.before with l4 := L4State.adaptDown step.before.l4 step.before.l3 }
  | TransKind.Stutter =>
      step.after = step.before

/-! ## Reachability Predicate -/
/--
A state is reachable if there exists an execution trace from the initial state.
This is the foundation for inductive proofs over all possible system executions.
-/
inductive Reachable (maxDepth : Nat) : SystemState → Prop where
  /-- The initial state is reachable -/
  | init : Reachable maxDepth (SystemState.init maxDepth)
  /-- If s1 is reachable and s1→s2 is a valid step, then s2 is reachable -/
  | step : ∀ {s1 s2 : SystemState} {t : TransKind},
      Reachable maxDepth s1 →
      isValidStep { before := s1, after := s2, transition := t } →
      Reachable maxDepth s2


/-! ## System Invariant Definitions -/

/-- Helper: System invariant component for L1 -/
def systemInvariant_l1 (s : SystemState) : Prop := L1State.noCollapse s.l1

/-- Helper: System invariant component for L2 -/
def systemInvariant_l2 (s : SystemState) : Prop := L2State.typeInvariant s.l2

/-- Helper: System invariant component for L3 -/
def systemInvariant_l3 (s : SystemState) : Prop := L3State.typeInvariant s.l3

/-- Helper: System invariant component for L4 -/
def systemInvariant_l4 (s : SystemState) : Prop := L4State.typeInvariant s.l4

/-- Helper: System invariant component for wall -/
def systemInvariant_wall (s : SystemState) : Prop := s.l1.stability.val < wallActivateThreshold → s.l2.wall

/-- Helper: System invariant component for L3 liveness -/
def systemInvariant_liveness (s : SystemState) : Prop := L3State.liveness s.l3 s.l1 s.l2

/-! ## Initial State Invariant Theorems -/

/-- Initial L1 state satisfies noCollapse -/
theorem l1_noCollapse_init : L1State.noCollapse L1State.init := by
  unfold L1State.noCollapse L1State.init
  simp [Probability.one, L1State.stability]

/-- Initial L4 state satisfies typeInvariant -/
theorem l4_typeInvariant_init : L4State.typeInvariant L4State.init := by
  simp [L4State.typeInvariant, L4State.init]
  norm_num

/-- Helper lemma: Initial state satisfies all invariants -/
theorem init_satisfies_invariants (maxDepth : Nat) :
    systemInvariant_l1 (SystemState.init maxDepth) ∧
    systemInvariant_l2 (SystemState.init maxDepth) ∧
    systemInvariant_l3 (SystemState.init maxDepth) ∧
    systemInvariant_l4 (SystemState.init maxDepth) ∧
    systemInvariant_wall (SystemState.init maxDepth) ∧
    systemInvariant_liveness (SystemState.init maxDepth) := by
  constructor
  · exact l1_noCollapse_init
  · constructor
    · -- L2 type invariant: uncertainty in [0, 1]
      unfold systemInvariant_l2 L2State.typeInvariant
      simp [SystemState.init, L2State.init]
      norm_num
    · constructor
      · -- L3 type invariant: understanding in [0, 1]
        unfold systemInvariant_l3 L3State.typeInvariant
        simp [SystemState.init, L3State.init, Probability.zero]
      · constructor
        · exact l4_typeInvariant_init
        · constructor
          · -- wall invariant: stability < wallActivateThreshold → wall
            -- For initial state, stability = 1, so antecedent "1 < wallActivateThreshold" is false
            unfold systemInvariant_wall
            intro h
            simp [SystemState.init, L1State.init, Probability.one, wallActivateThreshold] at h
            -- Now h : 1 < 0.4, which is impossible
            norm_num at h
          · -- liveness: init has ticksSinceTransmission = 0 < livenessWindow = 10
            unfold systemInvariant_liveness L3State.liveness
            intro h_capable
            simp [SystemState.init, L3State.init, L3State.livenessWindow]

/-! ## Invariant Preservation Theorems -/

/-! ### Helper Lemmas for Min -/
/-- If both arguments to min are ≥ c, then the result is ≥ c -/
theorem min_ge_of_ge {a b c : ℝ} (ha : a ≥ c) (hb : b ≥ c) : min a b ≥ c := by
  -- Direct application of Mathlib's le_min lemma
  -- le_min: c ≤ a → c ≤ b → c ≤ min a b
  exact le_min ha hb

/-! ### L1 Transition Preservation -/

/-- L1MaintainStability preserves L1.noCollapse -/
theorem l1_maintainStability_preserves_noCollapse (s : SystemState) (h_inv : L1State.noCollapse s.l1) :
    L1State.noCollapse (L1State.maintainStability s.l1) := by
  -- Proof: maintainStability keeps stability > 0 because old stability > 0
  -- Key insight: min a b > 0 if both a > 0 and b > 0
  unfold L1State.noCollapse L1State.maintainStability
  dsimp only
  -- Case analysis on stress < 0.3
  split
  · -- stress < 0.3: stability becomes min 1 (old + 1/100)
    have h_old_gt_0 : s.l1.stability.val > 0 := h_inv
    have h_sum_pos : s.l1.stability.val + (1/100 : ℝ) > 0 := by linarith [h_old_gt_0]
    -- Use aesop to automatically solve min 1 (old + 1/100) > 0
    -- given that 1 > 0 and old + 1/100 > 0
    aesop
  · -- stress >= 0.3: stability becomes min 1 old
    have h_old_gt_0 : s.l1.stability.val > 0 := h_inv
    -- Use aesop to automatically solve min 1 old > 0
    -- given that 1 > 0 and old > 0
    aesop

/-! ### L2 Transition Preservation -/

/-- L2UpdateBeliefs preserves L2.typeInvariant -/
theorem l2_updateBeliefs_preserves_typeInvariant (s : SystemState) (h_inv : systemInvariant_l2 s) :
    systemInvariant_l2 { s with l2 := L2State.updateBeliefs s.l2 } := by
  -- updateBeliefs keeps uncertainty the same, so type invariant is preserved
  unfold systemInvariant_l2 L2State.updateBeliefs
  -- Need to show: (updateBeliefs s.l2).uncertainty.val ≥ 0 ∧ ... ≤ 1
  -- Since updateBeliefs keeps uncertainty unchanged, this is h_inv
  constructor
  · exact h_inv.1
  · exact h_inv.2

/-! ### L3 Transition Preservation -/

/-- L3Plan preserves L3.typeInvariant -/
theorem l3_plan_preserves_typeInvariant (s : SystemState) :
    L3State.typeInvariant (L3State.plan s.l3 s.l2) := by
  -- Plan only increases understanding, capped at 1, so [0, 1] invariant is preserved
  -- The plan function embeds the proof in its return value
  unfold L3State.typeInvariant
  constructor
  · exact (L3State.plan s.l3 s.l2).understanding.property.1
  · exact (L3State.plan s.l3 s.l2).understanding.property.2

/-- L3BlockWhenWallActive preserves L3.typeInvariant -/
theorem l3_blockWhenWallActive_preserves_typeInvariant (s : SystemState) :
    L3State.typeInvariant (L3State.blockWhenWallActive s.l3 s.l2) := by
  -- Blocking only changes blocked field, not understanding
  -- So the understanding bounds are preserved
  unfold L3State.typeInvariant L3State.blockWhenWallActive
  split
  · -- Wall active: blocked becomes true, but understanding unchanged
    constructor
    · exact s.l3.understanding.property.1
    · exact s.l3.understanding.property.2
  · -- Wall inactive: state unchanged
    constructor
    · exact s.l3.understanding.property.1
    · exact s.l3.understanding.property.2

/-- L3Transmit preserves L3.typeInvariant — only resets ticksSinceTransmission -/
theorem l3_transmit_preserves_typeInvariant (s : SystemState) :
    L3State.typeInvariant (L3State.transmit s.l3) := by
  unfold L3State.typeInvariant L3State.transmit
  constructor
  · exact s.l3.understanding.property.1
  · exact s.l3.understanding.property.2

/-- L3Transmit preserves liveness — resets counter to 0, trivially within window -/
theorem l3_transmit_preserves_liveness (s : SystemState)
    (h : L3State.liveness s.l3 s.l1 s.l2) :
    L3State.liveness (L3State.transmit s.l3) s.l1 s.l2 := by
  unfold L3State.liveness L3State.transmit L3State.livenessWindow
  intro h_capable
  norm_num

/-- L3Ping preserves L3.typeInvariant — structurally identical to transmit -/
theorem l3_ping_preserves_typeInvariant (s : SystemState) :
    L3State.typeInvariant (L3State.ping s.l3) := by
  unfold L3State.typeInvariant L3State.ping
  constructor
  · exact s.l3.understanding.property.1
  · exact s.l3.understanding.property.2

/-- L3Ping preserves liveness — resets counter to 0, trivially within window -/
theorem l3_ping_preserves_liveness (s : SystemState)
    (h : L3State.liveness s.l3 s.l1 s.l2) :
    L3State.liveness (L3State.ping s.l3) s.l1 s.l2 := by
  unfold L3State.liveness L3State.ping L3State.livenessWindow
  intro h_capable
  norm_num

/-- Transitions that don't touch L3/L1/L2 state preserve liveness trivially -/
theorem liveness_preserved_when_unchanged (s : SystemState)
    (h : L3State.liveness s.l3 s.l1 s.l2) :
    L3State.liveness s.l3 s.l1 s.l2 := h

/-- In the formal model, ticksSinceTransmission is always 0.
    Init sets it to 0, and transmit (the only modifier) resets it to 0.
    Proved by induction on Reachable. -/
theorem ticksSinceTransmission_always_zero {maxDepth : Nat}
    (s : SystemState) (h_reachable : Reachable maxDepth s) :
    s.l3.ticksSinceTransmission = 0 := by
  induction h_reachable
  case init =>
    simp [SystemState.init, L3State.init]
  case step s1 s2 t h_reach1 h_step ih =>
    cases t with
    | L1ReflexAction =>
        simp only [isValidStep] at h_step
        obtain ⟨_, heq⟩ := h_step
        rw [heq]; exact ih
    | L1HeuristicAction =>
        simp only [isValidStep] at h_step
        obtain ⟨_, heq⟩ := h_step
        rw [heq]; exact ih
    | L1MaintainStability =>
        simp only [isValidStep] at h_step
        rw [h_step]; exact ih
    | L2UpdateBeliefs =>
        simp only [isValidStep] at h_step
        rw [h_step]; exact ih
    | L2ActivateWall =>
        simp only [isValidStep] at h_step
        rw [h_step]; exact ih
    | L2DeactivateWall =>
        simp only [isValidStep] at h_step
        rw [h_step]; exact ih
    | L3Plan =>
        simp only [isValidStep] at h_step
        rw [h_step]
        -- plan doesn't change ticksSinceTransmission
        simp only [L3State.plan]; split <;> exact ih
    | L3BlockWhenWallActive =>
        simp only [isValidStep] at h_step
        rw [h_step]
        simp only [L3State.blockWhenWallActive]; split <;> exact ih
    | L3Transmit =>
        simp only [isValidStep] at h_step
        rw [h_step]
        simp [L3State.transmit]
    | L3Ping =>
        simp only [isValidStep] at h_step
        rw [h_step]
        simp [L3State.ping]
    | L4Observe =>
        simp only [isValidStep] at h_step
        rw [h_step]; exact ih
    | L4AdaptDown =>
        simp only [isValidStep] at h_step
        rw [h_step]; exact ih
    | Stutter =>
        simp only [isValidStep] at h_step
        rw [h_step]; exact ih

/-- Helper: liveness holds whenever ticksSinceTransmission = 0 (trivially < 10). -/
theorem liveness_of_counter_zero (s : SystemState)
    (h_zero : s.l3.ticksSinceTransmission = 0) :
    L3State.liveness s.l3 s.l1 s.l2 := by
  unfold L3State.liveness L3State.livenessWindow
  intro _
  omega

/-- activateWall preserves liveness: ticksSinceTransmission unchanged (on L3), always 0 < 10. -/
theorem l2_activateWall_preserves_liveness (s : SystemState)
    (_h : L3State.liveness s.l3 s.l1 s.l2)
    (h_zero : s.l3.ticksSinceTransmission = 0) :
    L3State.liveness s.l3 s.l1 (L2State.activateWall s.l2 s.l1) := by
  unfold L3State.liveness L3State.livenessWindow
  intro _
  omega

/-- deactivateWall preserves liveness: counter = 0, always < livenessWindow. -/
theorem l2_deactivateWall_preserves_liveness (s : SystemState)
    (_h : L3State.liveness s.l3 s.l1 s.l2)
    (h_zero : s.l3.ticksSinceTransmission = 0) :
    L3State.liveness s.l3 s.l1 (L2State.deactivateWall s.l2 s.l1) := by
  unfold L3State.liveness L3State.livenessWindow
  intro _
  omega

/-- blockWhenWallActive preserves liveness: counter = 0, always < livenessWindow. -/
theorem l3_blockWhenWallActive_preserves_liveness (s : SystemState)
    (_h : L3State.liveness s.l3 s.l1 s.l2)
    (h_zero : s.l3.ticksSinceTransmission = 0) :
    L3State.liveness (L3State.blockWhenWallActive s.l3 s.l2) s.l1 s.l2 := by
  unfold L3State.liveness L3State.livenessWindow
  intro _
  simp only [L3State.blockWhenWallActive]
  split <;> simp [h_zero] <;> omega

/-! ### L4 Transition Preservation -/

/-- L4Observe preserves L4.typeInvariant -/
theorem l4_observe_preserves_typeInvariant (s : SystemState) :
    L4State.typeInvariant (L4State.observe s.l4 s.l3) := by
  -- The observe function embeds the proof in its return value
  unfold L4State.typeInvariant
  constructor
  · exact (L4State.observe s.l4 s.l3).hypothesisQualityThreshold.property.1
  · constructor
    · exact (L4State.observe s.l4 s.l3).hypothesisQualityThreshold.property.2
    · constructor
      · exact (L4State.observe s.l4 s.l3).learningRate.property.1
      · exact (L4State.observe s.l4 s.l3).learningRate.property.2

/-- L4AdaptDown preserves L4.typeInvariant -/
theorem l4_adaptDown_preserves_typeInvariant (s : SystemState) :
    L4State.typeInvariant (L4State.adaptDown s.l4 s.l3) := by
  -- The adaptDown function embeds the proof in its return value
  unfold L4State.typeInvariant
  constructor
  · exact (L4State.adaptDown s.l4 s.l3).hypothesisQualityThreshold.property.1
  · constructor
    · exact (L4State.adaptDown s.l4 s.l3).hypothesisQualityThreshold.property.2
    · constructor
      · exact (L4State.adaptDown s.l4 s.l3).learningRate.property.1
      · exact (L4State.adaptDown s.l4 s.l3).learningRate.property.2

/-! ### Full System Invariant Preservation -/

/-- A valid L1MaintainStability step preserves all system invariants -/
theorem l1_maintainStability_preserves_invariants (s : SystemState)
    {maxDepth : Nat} (h_reach : Transition.Reachable maxDepth s) :
    systemInvariant_l1 s →
    systemInvariant_l2 s →
    systemInvariant_l3 s →
    systemInvariant_l4 s →
    systemInvariant_wall s →
    L3State.liveness s.l3 s.l1 s.l2 →
    let s' := { s with l1 := L1State.maintainStability s.l1 }
    systemInvariant_l1 s' ∧
    systemInvariant_l2 s' ∧
    systemInvariant_l3 s' ∧
    systemInvariant_l4 s' ∧
    systemInvariant_wall s' ∧
    L3State.liveness s'.l3 s'.l1 s'.l2 := by
  intro h1 h2 h3 h4 hw hl
  constructor
  · -- L1: noCollapse preserved by maintainStability
    exact l1_maintainStability_preserves_noCollapse s h1
  · -- L2, L3, L4 unchanged, so their invariants preserved
    constructor
    · -- L2 invariant: s'.l2 = s.l2, so invariant holds
      unfold systemInvariant_l2
      exact h2
    · constructor
      · -- L3 invariant: s'.l3 = s.l3, so invariant holds
        unfold systemInvariant_l3
        exact h3
      · constructor
        · -- L4 invariant: s'.l4 = s.l4, so invariant holds
          unfold systemInvariant_l4
          exact h4
        · constructor
          · -- Wall invariant: need to prove s'.l1.stability < 0.4 → s'.l2.wall
            unfold systemInvariant_wall
            intro h_stability
            -- s'.l2 = s.l2, so need to prove s.l1.stability < wallActivateThreshold (to apply hw)
            -- Unfold the named constant so the rest of the proof works with numerics
            have h_old_lt_wat : s.l1.stability.val < wallActivateThreshold := by
              by_contra h_old_ge
              push_neg at h_old_ge
              simp [wallActivateThreshold] at h_old_ge h_stability
              -- By cases on stress < 0.3 (the branch in maintainStability)
              by_cases h_stress : s.l1.stress.val < 0.3
              · -- Case stress < 0.3: s'.stability = min 1 (s.stability + 1/100)
                have h_sum_ge : s.l1.stability.val + (1/100 : ℝ) ≥ 0.4 := by linarith
                have h_one_ge : (1 : ℝ) ≥ 0.4 := by norm_num
                have h_sprime_ge : min 1 (s.l1.stability.val + (1/100 : ℝ)) ≥ 0.4 := by
                  exact min_ge_of_ge h_one_ge h_sum_ge
                dsimp only [L1State.maintainStability] at h_stability
                rw [if_pos h_stress] at h_stability
                linarith [h_stability, h_sprime_ge]
              · -- Case stress >= 0.3: s'.stability = min 1 s.stability
                have h_one_ge : (1 : ℝ) ≥ 0.4 := by norm_num
                have h_sprime_ge : min 1 s.l1.stability.val ≥ 0.4 := by
                  exact min_ge_of_ge h_one_ge h_old_ge
                dsimp only [L1State.maintainStability] at h_stability
                rw [if_neg h_stress] at h_stability
                linarith [h_stability, h_sprime_ge]
            exact hw h_old_lt_wat
          · -- Liveness: L3 state untouched (s'.l3 = s.l3), so counter unchanged.
            -- The liveness implication: if new state capable, need counter < window.
            -- Since L3 unchanged, counter = s.l3.ticksSinceTransmission.
            -- By hl (old liveness), if old state was capable then counter < window.
            -- If old state was not capable, counter was never incremented (only transmit
            -- changes it, resetting to 0), so counter = 0 < livenessWindow.
            unfold L3State.liveness at *
            intro h_capable
            by_cases h_old_capable : ¬s.l3.blocked ∧ ¬s.l2.wall ∧ s.l1.stability.val ≥ wallActivateThreshold
            · -- Old state was also capable: old liveness gives counter < window
              exact hl h_old_capable
            · -- Old state was not capable: ticksSinceTransmission = 0 by induction
              -- on reachable states (no transition increments it, only transmit resets to 0).
              have h_counter_zero : s.l3.ticksSinceTransmission = 0 :=
                ticksSinceTransmission_always_zero s h_reach
              rw [h_counter_zero]
              exact L3State.livenessWindow_pos

/-- A valid L2UpdateBeliefs step preserves all system invariants -/
theorem l2_updateBeliefs_preserves_invariants (s : SystemState)
    (h1 : systemInvariant_l1 s)
    (h2 : systemInvariant_l2 s)
    (h3 : systemInvariant_l3 s)
    (h4 : systemInvariant_l4 s)
    (hw : systemInvariant_wall s)
    (hl : L3State.liveness s.l3 s.l1 s.l2) :
    let s' := { s with l2 := L2State.updateBeliefs s.l2 }
    systemInvariant_l1 s' ∧
    systemInvariant_l2 s' ∧
    systemInvariant_l3 s' ∧
    systemInvariant_l4 s' ∧
    systemInvariant_wall s' ∧
    L3State.liveness s'.l3 s'.l1 s'.l2 := by
  -- updateBeliefs keeps uncertainty and wall the same, L1/L3/L4 unchanged
  constructor
  · -- L1 invariant: s'.l1 = s.l1
    unfold systemInvariant_l1
    exact h1
  · constructor
    · -- L2 invariant: preserved by updateBeliefs
      unfold systemInvariant_l2 L2State.updateBeliefs
      exact h2
    · constructor
      · -- L3 invariant: s'.l3 = s.l3
        unfold systemInvariant_l3
        exact h3
      · constructor
        · -- L4 invariant: s'.l4 = s.l4
          unfold systemInvariant_l4
          exact h4
        · constructor
          · -- Wall invariant: s'.l1 = s.l1 and s'.l2.wall = s.l2.wall
            unfold systemInvariant_wall
            intro h_stability
            exact hw h_stability
          · -- Liveness: L1 and L3 unchanged, L2.updateBeliefs doesn't change wall,
            -- so the capability condition is identical → liveness preserved
            exact hl

/-! ## L2 Wall Transition Preservation Helpers -/

/-- activateWall preserves L2.typeInvariant (only changes wall, not uncertainty) -/
theorem l2_activateWall_preserves_typeInvariant (s : SystemState) (h : systemInvariant_l2 s) :
    systemInvariant_l2 { s with l2 := L2State.activateWall s.l2 s.l1 } := by
  unfold systemInvariant_l2 L2State.typeInvariant L2State.activateWall
  split <;> exact h

/-- deactivateWall preserves L2.typeInvariant -/
theorem l2_deactivateWall_preserves_typeInvariant (s : SystemState) (h : systemInvariant_l2 s) :
    systemInvariant_l2 { s with l2 := L2State.deactivateWall s.l2 s.l1 } := by
  unfold systemInvariant_l2 L2State.typeInvariant L2State.deactivateWall
  split <;> exact h

/-- activateWall preserves the wall invariant -/
theorem l2_activateWall_preserves_wall (s : SystemState) (hw : systemInvariant_wall s) :
    systemInvariant_wall { s with l2 := L2State.activateWall s.l2 s.l1 } := by
  unfold systemInvariant_wall
  intro hst
  simp only [L2State.activateWall, wallActivateThreshold]
  split
  · rfl
  · contradiction

/-- deactivateWall preserves the wall invariant.
    deactivateWall only sets wall := false when stability > wallDeactivateThreshold.
    The wall invariant triggers at stability < wallActivateThreshold.
    These two conditions cannot hold simultaneously (wallActivateThreshold < wallDeactivateThreshold). -/
theorem l2_deactivateWall_preserves_wall (s : SystemState) (hw : systemInvariant_wall s) :
    systemInvariant_wall { s with l2 := L2State.deactivateWall s.l2 s.l1 } := by
  unfold systemInvariant_wall
  intro hst
  simp only [L2State.deactivateWall, wallDeactivateThreshold, wallActivateThreshold]
  split
  · -- Branch: s.l1.stability.val > 0.6, but hst says < 0.4 — contradiction.
    next h_gt =>
      dsimp only at hst
      norm_num at h_gt hst
      linarith
  · -- Branch: else (state unchanged), wall preserved
    exact hw hst

/-! ## Inductive Invariant Theorem -/
/--
All reachable states satisfy the system invariant.
This is proved by induction on the Reachable predicate.

Proof sketch:
- Base case: Initial state satisfies all invariants (proved)
- Inductive step: Each transition preserves all invariants (requires per-transition proofs)
-/
theorem all_reachable_states_satisfy_invariant {maxDepth : Nat}
    (s : SystemState)
    (h_reachable : Reachable maxDepth s) :
    systemInvariant_l1 s ∧
    systemInvariant_l2 s ∧
    systemInvariant_l3 s ∧
    systemInvariant_l4 s ∧
    systemInvariant_wall s ∧
    systemInvariant_liveness s := by
  -- Use induction on the Reachable predicate
  induction h_reachable
  case init =>
      -- Base case: s is SystemState.init maxDepth
      exact init_satisfies_invariants maxDepth
  case step s1 s2 transition h_reach1 h_step ih =>
      -- ih : all invariants hold for s1 (inductive hypothesis)
      -- h_step : isValidStep { before := s1, after := s2, transition := transition }
      cases transition with
      | L1ReflexAction =>
          simp only [isValidStep] at h_step
          obtain ⟨hcan, heq⟩ := h_step
          rw [heq]
          exact ⟨ih.1, ih.2.1, ih.2.2.1, ih.2.2.2.1, ih.2.2.2.2.1, ih.2.2.2.2.2⟩
      | L1HeuristicAction =>
          simp only [isValidStep] at h_step
          obtain ⟨hcan, heq⟩ := h_step
          rw [heq]
          exact ⟨ih.1, ih.2.1, ih.2.2.1, ih.2.2.2.1, ih.2.2.2.2.1, ih.2.2.2.2.2⟩
      | L1MaintainStability =>
          simp only [isValidStep] at h_step
          rw [h_step]
          exact l1_maintainStability_preserves_invariants s1 h_reach1 ih.1 ih.2.1 ih.2.2.1 ih.2.2.2.1 ih.2.2.2.2.1 ih.2.2.2.2.2
      | L2UpdateBeliefs =>
          simp only [isValidStep] at h_step
          rw [h_step]
          exact l2_updateBeliefs_preserves_invariants s1 ih.1 ih.2.1 ih.2.2.1 ih.2.2.2.1 ih.2.2.2.2.1 ih.2.2.2.2.2
      | L2ActivateWall =>
          simp only [isValidStep] at h_step
          rw [h_step]
          exact ⟨ih.1,
                 l2_activateWall_preserves_typeInvariant s1 ih.2.1,
                 ih.2.2.1,
                 ih.2.2.2.1,
                 l2_activateWall_preserves_wall s1 ih.2.2.2.2.1,
                 l2_activateWall_preserves_liveness s1 ih.2.2.2.2.2
                   (ticksSinceTransmission_always_zero s1 h_reach1)⟩
      | L2DeactivateWall =>
          simp only [isValidStep] at h_step
          rw [h_step]
          exact ⟨ih.1,
                 l2_deactivateWall_preserves_typeInvariant s1 ih.2.1,
                 ih.2.2.1,
                 ih.2.2.2.1,
                 l2_deactivateWall_preserves_wall s1 ih.2.2.2.2.1,
                 l2_deactivateWall_preserves_liveness s1 ih.2.2.2.2.2
                   (ticksSinceTransmission_always_zero s1 h_reach1)⟩
      | L3Plan =>
          simp only [isValidStep] at h_step
          rw [h_step]
          -- plan doesn't change ticksSinceTransmission or blocked, liveness holds trivially (counter=0)
          have h_zero := ticksSinceTransmission_always_zero s1 h_reach1
          exact ⟨ih.1, ih.2.1, l3_plan_preserves_typeInvariant s1, ih.2.2.2.1, ih.2.2.2.2.1,
                 liveness_of_counter_zero { s1 with l3 := L3State.plan s1.l3 s1.l2 }
                   (by simp only [L3State.plan]; split <;> simp [h_zero])⟩
      | L3BlockWhenWallActive =>
          simp only [isValidStep] at h_step
          rw [h_step]
          exact ⟨ih.1, ih.2.1, l3_blockWhenWallActive_preserves_typeInvariant s1, ih.2.2.2.1, ih.2.2.2.2.1,
                 l3_blockWhenWallActive_preserves_liveness s1 ih.2.2.2.2.2
                   (ticksSinceTransmission_always_zero s1 h_reach1)⟩
      | L3Transmit =>
          simp only [isValidStep] at h_step
          rw [h_step]
          -- L3Transmit resets ticksSinceTransmission to 0, preserves typeInvariant and liveness
          exact ⟨ih.1, ih.2.1, l3_transmit_preserves_typeInvariant s1, ih.2.2.2.1, ih.2.2.2.2.1,
                 l3_transmit_preserves_liveness s1 ih.2.2.2.2.2⟩
      | L3Ping =>
          simp only [isValidStep] at h_step
          rw [h_step]
          -- L3Ping resets ticksSinceTransmission to 0 without transmitting understanding
          exact ⟨ih.1, ih.2.1, l3_ping_preserves_typeInvariant s1, ih.2.2.2.1, ih.2.2.2.2.1,
                 l3_ping_preserves_liveness s1 ih.2.2.2.2.2⟩
      | L4Observe =>
          simp only [isValidStep] at h_step
          rw [h_step]
          exact ⟨ih.1, ih.2.1, ih.2.2.1, l4_observe_preserves_typeInvariant s1, ih.2.2.2.2.1, ih.2.2.2.2.2⟩
      | L4AdaptDown =>
          simp only [isValidStep] at h_step
          rw [h_step]
          exact ⟨ih.1, ih.2.1, ih.2.2.1, l4_adaptDown_preserves_typeInvariant s1, ih.2.2.2.2.1, ih.2.2.2.2.2⟩
      | Stutter =>
          simp only [isValidStep] at h_step
          rw [h_step]
          exact ih

/-! ## Transition Relation Theorems -/


/-! ## Transition Helper Lemmas -/

/-- Helper: When stability < wallActivateThreshold, activateWall results in wall = true -/
theorem activateWall_makes_wall_true
    (s : SystemState)
    (h_stability : s.l1.stability.val < wallActivateThreshold) :
    (L2State.activateWall s.l2 s.l1).wall = true := by
  unfold L2State.activateWall
  simp only [h_stability, Bool.or_true, wallActivateThreshold]
  split
  · rfl
  · rename_i h_not_lt
    contradiction

/-- Helper: If wall is true, then applying blockWhenWallActive results in blocked = true -/
theorem wall_implies_blocked_after_transition
    (s : SystemState) :
    s.l2.wall = true →
    (L3State.blockWhenWallActive s.l3 s.l2).blocked = true := by
  unfold L3State.blockWhenWallActive
  intro h_wall
  split
  · -- Wall active: blocked becomes true
    rfl
  · -- Wall inactive - contradicts h_wall
    simp only [h_wall]

/-! ## Main Theorem: L3 not blocked implies wall is false -/

/-- When L3 is not blocked in a reachable state, the wall must be inactive.
    Proof by induction on Reachable with case analysis on TransKind. -/
theorem l3_not_blocked_implies_wall_false
    (maxDepth : Nat) (s : SystemState)
    (h_reachable : Reachable maxDepth s)
    (h_l1_inv : L1State.noCollapse s.l1)
    (h_l2_inv : L2State.typeInvariant s.l2)
    (h_l3_inv : L3State.typeInvariant s.l3)
    (h_l4_inv : L4State.typeInvariant s.l4)
    (h_wall_inv : s.l1.stability.val < 0.4 → s.l2.wall)
    (h_blocked : s.l3.blocked = false) :
    s.l2.wall = false := by
  induction h_reachable
  case init =>
    simp [SystemState.init, L2State.init, L3State.init]
  case step s1 s2 t h_reach1 h_step ih =>
    cases t with
    | L1ReflexAction =>
        -- Only changes l1. l2, l3, l4 unchanged.
        simp only [isValidStep] at h_step
        obtain ⟨hcan, heq⟩ := h_step
        have h_l2_eq : s2.l2 = s1.l2 := by simp [heq]
        have h_l3_eq : s2.l3 = s1.l3 := by simp [heq]
        have h_inv := all_reachable_states_satisfy_invariant s1 h_reach1
        have h_s1_blocked : s1.l3.blocked = false := by rw [← h_l3_eq]; exact h_blocked
        have h_s1_wall := ih h_inv.1 h_inv.2.1 h_inv.2.2.1 h_inv.2.2.2.1 h_inv.2.2.2.2.1 h_s1_blocked
        rw [h_l2_eq]; exact h_s1_wall
    | L1HeuristicAction =>
        simp only [isValidStep] at h_step
        obtain ⟨hcan, heq⟩ := h_step
        have h_l2_eq : s2.l2 = s1.l2 := by simp [heq]
        have h_l3_eq : s2.l3 = s1.l3 := by simp [heq]
        have h_inv := all_reachable_states_satisfy_invariant s1 h_reach1
        have h_s1_blocked : s1.l3.blocked = false := by rw [← h_l3_eq]; exact h_blocked
        have h_s1_wall := ih h_inv.1 h_inv.2.1 h_inv.2.2.1 h_inv.2.2.2.1 h_inv.2.2.2.2.1 h_s1_blocked
        rw [h_l2_eq]; exact h_s1_wall
    | L1MaintainStability =>
        simp only [isValidStep] at h_step
        have h_l3_eq : s2.l3 = s1.l3 := by simp [h_step]
        have h_l2_eq : s2.l2 = s1.l2 := by simp [h_step]
        have h_inv := all_reachable_states_satisfy_invariant s1 h_reach1
        have h_s1_blocked : s1.l3.blocked = false := by rw [← h_l3_eq]; exact h_blocked
        have h_s1_wall := ih h_inv.1 h_inv.2.1 h_inv.2.2.1 h_inv.2.2.2.1 h_inv.2.2.2.2.1 h_s1_blocked
        rw [h_l2_eq]; exact h_s1_wall
    | L2UpdateBeliefs =>
        -- updateBeliefs changes l2 but wall is unchanged (placeholder)
        simp only [isValidStep] at h_step
        have h_l3_eq : s2.l3 = s1.l3 := by simp [h_step]
        have h_inv := all_reachable_states_satisfy_invariant s1 h_reach1
        have h_s1_blocked : s1.l3.blocked = false := by rw [← h_l3_eq]; exact h_blocked
        -- updateBeliefs doesn't change wall: { s with uncertainty := s.uncertainty }
        have h_wall_eq : s2.l2.wall = s1.l2.wall := by simp [h_step]; rfl
        have h_s1_wall := ih h_inv.1 h_inv.2.1 h_inv.2.2.1 h_inv.2.2.2.1 h_inv.2.2.2.2.1 h_s1_blocked
        rw [h_wall_eq]; exact h_s1_wall
    | L2ActivateWall =>
        -- activateWall: if stability < 0.4 then wall = true, else unchanged
        simp only [isValidStep] at h_step
        have h_l3_eq : s2.l3 = s1.l3 := by simp [h_step]
        have h_inv := all_reachable_states_satisfy_invariant s1 h_reach1
        have h_s1_blocked : s1.l3.blocked = false := by rw [← h_l3_eq]; exact h_blocked
        have h_s1_wall := ih h_inv.1 h_inv.2.1 h_inv.2.2.1 h_inv.2.2.2.1 h_inv.2.2.2.2.1 h_s1_blocked
        -- s2.l2.wall is activateWall result
        simp only [h_step, L2State.activateWall]
        split
        · -- stability < 0.4: wall = true. But IH says s1.l2.wall = false.
          -- And wall_inv says stability < 0.4 → s1.l2.wall. Contradiction!
          next h_low =>
            have h_wall_true := h_inv.2.2.2.2.1 h_low
            rw [h_s1_wall] at h_wall_true
            -- h_wall_true : false = true → derive False
            exact absurd h_wall_true Bool.false_ne_true
        · -- stability ≥ 0.4: wall unchanged = s1.l2.wall = false
          exact h_s1_wall
    | L2DeactivateWall =>
        -- deactivateWall: if stability > 0.6 then wall = false, else unchanged
        simp only [isValidStep] at h_step
        have h_l3_eq : s2.l3 = s1.l3 := by simp [h_step]
        have h_inv := all_reachable_states_satisfy_invariant s1 h_reach1
        have h_s1_blocked : s1.l3.blocked = false := by rw [← h_l3_eq]; exact h_blocked
        have h_s1_wall := ih h_inv.1 h_inv.2.1 h_inv.2.2.1 h_inv.2.2.2.1 h_inv.2.2.2.2.1 h_s1_blocked
        simp only [h_step, L2State.deactivateWall]
        split
        · -- stability > 0.6: wall = false directly
          rfl
        · -- stability ≤ 0.6: wall unchanged = s1.l2.wall = false
          exact h_s1_wall
    | L3Plan =>
        -- plan changes l3.understanding but not l3.blocked. l2 unchanged.
        simp only [isValidStep] at h_step
        have h_l2_eq : s2.l2 = s1.l2 := by simp [h_step]
        -- plan doesn't change blocked
        have h_blocked_eq : s2.l3.blocked = s1.l3.blocked := by
          rw [h_step]; simp only [L3State.plan]; split <;> rfl
        have h_inv := all_reachable_states_satisfy_invariant s1 h_reach1
        have h_s1_blocked : s1.l3.blocked = false := by rw [← h_blocked_eq]; exact h_blocked
        have h_s1_wall := ih h_inv.1 h_inv.2.1 h_inv.2.2.1 h_inv.2.2.2.1 h_inv.2.2.2.2.1 h_s1_blocked
        rw [h_l2_eq]; exact h_s1_wall
    | L3BlockWhenWallActive =>
        -- blockWhenWallActive: if s1.l2.wall then blocked := true else unchanged
        -- h_blocked: s2.l3.blocked = false
        -- After applying h_step: (L3State.blockWhenWallActive s1.l3 s1.l2).blocked = false
        -- If wall: blocked = true, contradiction. If ¬wall: blocked unchanged.
        simp only [isValidStep] at h_step
        have h_l2_eq : s2.l2 = s1.l2 := by simp [h_step]
        -- Rewrite h_blocked using h_step to get blocked of blockWhenWallActive result
        have h_blocked' : (L3State.blockWhenWallActive s1.l3 s1.l2).blocked = false := by
          simp only [h_step] at h_blocked; exact h_blocked
        -- Now case-split on the if in blockWhenWallActive
        simp only [L3State.blockWhenWallActive] at h_blocked'
        split at h_blocked'
        · -- wall = true: blocked = true, but h_blocked' says blocked = false
          next h_wall_true =>
            cases h_blocked'
        · -- wall = false: blocked unchanged. Wall is false.
          next h_wall_false =>
            -- h_wall_false : ¬(s1.l2.wall = true). Goal: s2.l2.wall = false
            -- Since s2.l2 = s1.l2 (from h_l2_eq), just need s1.l2.wall = false
            -- From h_wall_false and Bool discreteness
            rw [h_l2_eq]
            exact eq_false_of_ne_true h_wall_false
    | L3Transmit =>
        -- L3Transmit only resets ticksSinceTransmission. l2 unchanged, blocked unchanged.
        simp only [isValidStep] at h_step
        have h_l2_eq : s2.l2 = s1.l2 := by simp [h_step]
        have h_blocked_eq : s2.l3.blocked = s1.l3.blocked := by
          simp [h_step, L3State.transmit]
        have h_inv := all_reachable_states_satisfy_invariant s1 h_reach1
        have h_s1_blocked : s1.l3.blocked = false := by rw [← h_blocked_eq]; exact h_blocked
        have h_s1_wall := ih h_inv.1 h_inv.2.1 h_inv.2.2.1 h_inv.2.2.2.1 h_inv.2.2.2.2.1 h_s1_blocked
        rw [h_l2_eq]; exact h_s1_wall
    | L3Ping =>
        -- L3Ping only resets ticksSinceTransmission. l2 unchanged, blocked unchanged.
        simp only [isValidStep] at h_step
        have h_l2_eq : s2.l2 = s1.l2 := by simp [h_step]
        have h_blocked_eq : s2.l3.blocked = s1.l3.blocked := by
          simp [h_step, L3State.ping]
        have h_inv := all_reachable_states_satisfy_invariant s1 h_reach1
        have h_s1_blocked : s1.l3.blocked = false := by rw [← h_blocked_eq]; exact h_blocked
        have h_s1_wall := ih h_inv.1 h_inv.2.1 h_inv.2.2.1 h_inv.2.2.2.1 h_inv.2.2.2.2.1 h_s1_blocked
        rw [h_l2_eq]; exact h_s1_wall
    | L4Observe =>
        -- Only changes l4. l2 and l3 unchanged.
        simp only [isValidStep] at h_step
        have h_l2_eq : s2.l2 = s1.l2 := by simp [h_step]
        have h_l3_eq : s2.l3 = s1.l3 := by simp [h_step]
        have h_inv := all_reachable_states_satisfy_invariant s1 h_reach1
        have h_s1_blocked : s1.l3.blocked = false := by rw [← h_l3_eq]; exact h_blocked
        have h_s1_wall := ih h_inv.1 h_inv.2.1 h_inv.2.2.1 h_inv.2.2.2.1 h_inv.2.2.2.2.1 h_s1_blocked
        rw [h_l2_eq]; exact h_s1_wall
    | L4AdaptDown =>
        -- Only changes l4. l2 and l3 unchanged.
        simp only [isValidStep] at h_step
        have h_l2_eq : s2.l2 = s1.l2 := by simp [h_step]
        have h_l3_eq : s2.l3 = s1.l3 := by simp [h_step]
        have h_inv := all_reachable_states_satisfy_invariant s1 h_reach1
        have h_s1_blocked : s1.l3.blocked = false := by rw [← h_l3_eq]; exact h_blocked
        have h_s1_wall := ih h_inv.1 h_inv.2.1 h_inv.2.2.1 h_inv.2.2.2.1 h_inv.2.2.2.2.1 h_s1_blocked
        rw [h_l2_eq]; exact h_s1_wall
    | Stutter =>
        -- Stutter: s2 = s1. All invariants preserved trivially.
        simp only [isValidStep] at h_step
        subst h_step
        exact ih h_l1_inv h_l2_inv h_l3_inv h_l4_inv h_wall_inv h_blocked

/-! ## Axiom: Wall ↔ Blocked Invariant -/

-- Duplicate of l3_not_blocked_implies_wall_false for backward compatibility.
-- The proof is now complete — this was previously blocked on string-based transition matching.
theorem l3_not_blocked_implies_wall_false_axiom
    (maxDepth : Nat) (s : SystemState)
    (h_reachable : Reachable maxDepth s)
    (h_l1_inv : L1State.noCollapse s.l1)
    (h_l2_inv : L2State.typeInvariant s.l2)
    (h_l3_inv : L3State.typeInvariant s.l3)
    (h_l4_inv : L4State.typeInvariant s.l4)
    (h_wall_inv : s.l1.stability.val < 0.4 → s.l2.wall)
    (h_blocked : s.l3.blocked = false) :
    s.l2.wall = false :=
  l3_not_blocked_implies_wall_false maxDepth s h_reachable h_l1_inv h_l2_inv h_l3_inv h_l4_inv h_wall_inv h_blocked

/-- Corollary: wall → blocked for reachable states (contrapositive) -/
theorem wall_implies_blocked_for_reachable
    (maxDepth : Nat) (s : SystemState)
    (h_reachable : Reachable maxDepth s)
    (h_l1_inv : L1State.noCollapse s.l1)
    (h_l2_inv : L2State.typeInvariant s.l2)
    (h_l3_inv : L3State.typeInvariant s.l3)
    (h_l4_inv : L4State.typeInvariant s.l4)
    (h_wall_inv : s.l1.stability.val < 0.4 → s.l2.wall)
    (h_wall : s.l2.wall = true) :
    s.l3.blocked = true := by
  -- Contrapositive of l3_not_blocked_implies_wall_false:
  -- If blocked = false → wall = false, then wall = true → blocked = true
  by_contra h_not_blocked
  -- h_not_blocked : s.l3.blocked ≠ true, so s.l3.blocked = false
  have h_blocked_false : s.l3.blocked = false := by
    cases h : s.l3.blocked with
    | true => exact absurd h h_not_blocked
    | false => rfl
  have h_wall_false := l3_not_blocked_implies_wall_false_axiom
    maxDepth s h_reachable h_l1_inv h_l2_inv h_l3_inv h_l4_inv h_wall_inv h_blocked_false
  rw [h_wall_false] at h_wall
  cases h_wall

/-! ## L1 Action Selection Theorems -/
-- Note: The action selection policy theorems (l1_idle_implies_stability_ge_05,
-- l1_idle_stability) are defined in Invariants.lean which imports this file.

/-- L3 yields when L1 is unstable (wall activates, causing L3 to be blocked) -/
theorem l3_yields_on_low_stability_transition
    (s : SystemState)
    (h_low_stability : s.l1.stability.val < 0.3) :
    (L3State.blockWhenWallActive s.l3 (L2State.activateWall s.l2 s.l1)).blocked = true := by
  /- Wall activates because stability < 0.3 < wallActivateThreshold -/
  unfold L3State.blockWhenWallActive
  simp only [L2State.activateWall]
  split
  · /- Wall activates (stability < wallActivateThreshold, true since < 0.3) -/
    simp only [Bool.or_eq_true]
    rfl
  · /- Wall doesn't activate - impossible since h_low_stability < 0.3 < wallActivateThreshold -/
    rename_i h_not_lt_wat
    /- h_not_lt_wat: ¬(s.l1.stability < wallActivateThreshold) -/
    /- Since 0.3 < 0.4 = wallActivateThreshold, h_low_stability implies < wallActivateThreshold -/
    have h_lt_wat : s.l1.stability.val < wallActivateThreshold := by
      simp [wallActivateThreshold]
      calc s.l1.stability.val
        _ < 0.3 := h_low_stability
        _ < 0.4 := by norm_num
    exact False.elim (h_not_lt_wat h_lt_wat)

/-- L4 can always observe or adapt (liveness) -/
theorem l4_can_always_act
    (s : SystemState)
    (h_l4_inv : L4State.typeInvariant s.l4) :
    ∃ s' : SystemState,
      L4State.typeInvariant s'.l4 ∧
      (s'.l4 = L4State.observe s.l4 s.l3 ∨ s'.l4 = L4State.adaptDown s.l4 s.l3) := by
  /- L4 can always either observe (when understanding ≥ 0.8) or adaptDown (when blocked) -/
  /- This is a liveness property: L4 is never permanently stuck -/
  /- We use the preservation theorems we've already proved -/
  by_cases h_blocked : s.l3.blocked
  · -- L3 blocked: use adaptDown
    use { s with l4 := L4State.adaptDown s.l4 s.l3 }
    constructor
    · -- Type invariant preserved by adaptDown
      exact l4_adaptDown_preserves_typeInvariant s
    · -- s'.l4 = adaptDown
      apply Or.inr
      rfl
  · -- L3 not blocked
    by_cases h_understanding : s.l3.understanding.val ≥ 0.8
    · -- High understanding: use observe
      use { s with l4 := L4State.observe s.l4 s.l3 }
      constructor
      · -- Type invariant preserved by observe
        exact l4_observe_preserves_typeInvariant s
      · -- s'.l4 = observe
        apply Or.inl
        rfl
    · -- Low understanding and not blocked: use adaptDown
      use { s with l4 := L4State.adaptDown s.l4 s.l3 }
      constructor
      · -- Type invariant preserved by adaptDown
        exact l4_adaptDown_preserves_typeInvariant s
      · -- s'.l4 = adaptDown
        apply Or.inr
        rfl

end Transition

end EvoEcos

end
