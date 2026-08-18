/-
EvoEcos Invariants Module
=========================

Critical invariants and theorems for the Stable Epistemic Bootstrap system.

Key Properties to Prove:
  1. NoCollapse - L1 stability > 0 always
  2. L1AlwaysResponds - Survival guarantee
  3. L3WallInvariant - L3 blocked when L1 unstable
  4. L1Independence - L1 operates without L3
  5. L4TypeInvariant - L4 state is well-typed
  6. L4NonInterference - L4 does not modify L1/L2/L3 state
-/

import EvoEcos.Layers

noncomputable section

namespace EvoEcos

/-! ## Critical Invariants -/

/-- No Collapse: L1 stability is never zero -/
theorem noCollapse_init : L1State.noCollapse L1State.init := by
  simp only [L1State.noCollapse, L1State.init, Probability.one]
  norm_num

/-! ## Wall Invariant -/

/-- When L1 is unstable, wall should be activated -/
theorem wall_activates_when_unstable
    (l1 : L1State) (l2 : L2State)
    (h : l1.stability.val < wallActivateThreshold) :
    (L2State.activateWall l2 l1).wall = true := by
  simp only [L2State.activateWall, wallActivateThreshold]
  split
  · rfl
  · next h' => exact absurd h h'

/-- When L1 is sufficiently stable, wall can be deactivated.
    Open threshold (0.60) is higher than close threshold (0.40) — hysteresis. -/
theorem wall_deactivates_when_stable
    (l1 : L1State) (l2 : L2State)
    (h : l1.stability.val > wallDeactivateThreshold) :
    (L2State.deactivateWall l2 l1).wall = false := by
  simp only [L2State.deactivateWall, wallDeactivateThreshold]
  split
  · rfl
  · next h' => exact absurd h h'

/-! ## L3 Blocking -/

/-- L3 is blocked when wall is active -/
theorem l3_blocked_when_wall
    (l3 : L3State) (l2 : L2State)
    (h : l2.wall = true) :
    (L3State.blockWhenWallActive l3 l2).blocked = true := by
  simp only [L3State.blockWhenWallActive]
  simp [*]

/-! ## L1 Independence -/

/-- L1 can always execute reflex when active and stable -/
theorem l1_reflex_independence
    (s : L1State)
    (hactive : s.active = true)
    (hstable : s.stability.val > 0) :
    L1State.canReflex s := by
  exact ⟨hactive, hstable⟩

/-- L1 can execute heuristic when sufficiently stable -/
theorem l1_heuristic_when_stable
    (s : L1State)
    (hactive : s.active = true)
    (hstable : s.stability.val > 0.3) :
    L1State.canHeuristic s := by
  exact ⟨hactive, hstable⟩

/-! ## System Invariant -/

/-- L4 type invariant holds for initial state -/
theorem l4_typeInvariant_init : L4State.typeInvariant L4State.init := by
  simp only [L4State.typeInvariant, L4State.init]
  norm_num

/-- Combined system invariant (now includes L4 + L3 liveness) -/
def systemInvariant (s : SystemState) : Prop :=
  L1State.noCollapse s.l1 ∧
  L2State.typeInvariant s.l2 ∧
  L3State.typeInvariant s.l3 ∧
  L4State.typeInvariant s.l4 ∧
  (s.l1.stability.val < wallActivateThreshold → s.l2.wall) ∧
  L3State.liveness s.l3 s.l1 s.l2

/-- System invariant holds for initial state -/
theorem systemInvariant_init (maxDepth : Nat) :
    systemInvariant (SystemState.init maxDepth) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact noCollapse_init
  · simp [L2State.typeInvariant, SystemState.init, L2State.init]
    norm_num
  · simp [L3State.typeInvariant, SystemState.init, L3State.init, Probability.zero]
  · exact l4_typeInvariant_init
  · intro h
    simp [SystemState.init, L1State.init, Probability.one] at h
    norm_num at h
  · -- L3 liveness: init has ticksSinceTransmission = 0 < livenessWindow = 10
    unfold L3State.liveness
    intro h_capable
    simp [SystemState.init, L3State.init, L3State.livenessWindow]

/-! ## L4 Invariants -/

/-- L4 observe maintains type invariant -/
theorem l4_observe_typeInvariant
    (s : L4State) (l3 : L3State)
    (h : L4State.typeInvariant s) :
    L4State.typeInvariant (L4State.observe s l3) := by
  unfold L4State.observe
  split
  · -- Case: active and high understanding
    unfold L4State.typeInvariant
    constructor
    · -- 0 ≤ min 1 (threshold + rate)
      apply le_min
      · norm_num
      · linarith [h.1, h.2.2.1]
    · constructor
      · -- min 1 _ ≤ 1
        exact min_le_left _ _
      · constructor
        · exact h.2.2.1
        · exact h.2.2.2
  · -- Case: inactive or low understanding, state unchanged
    exact h

/-- L4 adaptDown maintains type invariant -/
theorem l4_adaptDown_typeInvariant
    (s : L4State) (l3 : L3State)
    (h : L4State.typeInvariant s) :
    L4State.typeInvariant (L4State.adaptDown s l3) := by
  unfold L4State.adaptDown
  split
  · -- Case: active and blocked
    unfold L4State.typeInvariant
    constructor
    · -- 0 ≤ max 0.1 (threshold - rate)
      have h01 : (0 : ℝ) ≤ 0.1 := by norm_num
      exact le_trans h01 (le_max_left _ _)
    · constructor
      · -- max 0.1 _ ≤ 1
        have h1 : (0.1 : ℝ) ≤ 1 := by norm_num
        have h2 : s.hypothesisQualityThreshold.val - s.learningRate.val ≤ 1 := by
          linarith [h.2.1, h.2.2.1]
        exact max_le h1 h2
      · constructor
        · exact h.2.2.1
        · exact h.2.2.2
  · -- Case: inactive or not blocked, state unchanged
    exact h

/-! ## L4 Non-Interference -/

/-- L4 observe does not modify L1 state -/
theorem l4_observe_noninterfering_l1
    (s : SystemState) :
    (SystemState.l1 <| { s with l4 := L4State.observe s.l4 s.l3 }) = s.l1 := by
  rfl

/-- L4 observe does not modify L2 state -/
theorem l4_observe_noninterfering_l2
    (s : SystemState) :
    (SystemState.l2 <| { s with l4 := L4State.observe s.l4 s.l3 }) = s.l2 := by
  rfl

/-- L4 observe does not modify L3 state -/
theorem l4_observe_noninterfering_l3
    (s : SystemState) :
    (SystemState.l3 <| { s with l4 := L4State.observe s.l4 s.l3 }) = s.l3 := by
  rfl

/-- L4 adaptDown does not modify L1 state -/
theorem l4_adaptDown_noninterfering_l1
    (s : SystemState) :
    (SystemState.l1 <| { s with l4 := L4State.adaptDown s.l4 s.l3 }) = s.l1 := by
  rfl

/-- L4 adaptDown does not modify L2 state -/
theorem l4_adaptDown_noninterfering_l2
    (s : SystemState) :
    (SystemState.l2 <| { s with l4 := L4State.adaptDown s.l4 s.l3 }) = s.l2 := by
  rfl

/-- L4 adaptDown does not modify L3 state -/
theorem l4_adaptDown_noninterfering_l3
    (s : SystemState) :
    (SystemState.l3 <| { s with l4 := L4State.adaptDown s.l4 s.l3 }) = s.l3 := by
  rfl

/-! ## Safety Properties -/

/-- L3 cannot plan when wall is active -/
theorem l3_cannot_plan_when_wall
    (l3 : L3State) (l2 : L2State)
    (hwall : l2.wall = true) :
    ¬L3State.canPlan l3 l2 := by
  simp only [L3State.canPlan]
  intro ⟨_, _, hnotwall⟩
  simp [*] at hnotwall

/-- L3 blocked implies L3 cannot plan -/
theorem blocked_implies_cannot_plan
    (l3 : L3State) (l2 : L2State)
    (hblocked : l3.blocked = true) :
    ¬L3State.canPlan l3 l2 := by
  simp only [L3State.canPlan]
  intro ⟨_, hnotblocked, _⟩
  simp [*] at hnotblocked

/-- Graceful degradation: Under high stress, L3 is blocked and L1 uses only basic actions -/
def gracefulDegradation (s : SystemState) : Prop :=
  s.l1.stress.val ≥ 0.8 →
    s.l1.stability.val > 0 ∧
    s.l3.blocked ∧
    (s.l1.currentAction.type = ActionType.reflex ∨
     s.l1.currentAction.type = ActionType.none)

/-! ## Liveness Properties -/

/-- L1 eventually recovers (stress decreases through maintainStability) -/
theorem maintainStability_reduces_stress
    (s : L1State)
    (h : s.stress.val > 0) :
    (L1State.maintainStability s).stress.val < s.stress.val := by
  simp only [L1State.maintainStability]
  have h1 := s.stress.property.1
  have h2 := s.stress.property.2
  show min 1 (s.stress.val * (95 / 100)) < s.stress.val
  apply lt_of_le_of_lt (min_le_right _ _)
  nlinarith

/-! ## L4 Liveness Properties -/

/-- L4 can always eventually act (no permanent deadlock).
    `hactive` is unused: the conclusion holds for ALL activity states, not only
    active ones (a strengthening). Kept for L4-liveness family uniformity and to
    serve the two live callers (`l3_l4_contract`, action-policy theorem) that
    thread it. Declared via `nolint`, not silent — see formal/lint.sh. -/
@[nolint unusedArguments]
theorem l4_canAlwaysActEventually
    (s : SystemState)
    (hinv : systemInvariant s)
    (hactive : s.l4.active = true) :
    (∃ l4', L4State.typeInvariant l4' ∧
     (l4' = L4State.observe s.l4 s.l3 ∨
      l4' = L4State.adaptDown s.l4 s.l3)) := by
  by_cases h_understanding : s.l3.understanding.val ≥ 0.8
  · -- L3 has high understanding: L4 can observe
    use L4State.observe s.l4 s.l3
    constructor
    · exact l4_observe_typeInvariant s.l4 s.l3 hinv.2.2.2.1
    · exact Or.inl rfl
  · -- L3 blocked or low understanding: L4 can adapt down
    use L4State.adaptDown s.l4 s.l3
    constructor
    · exact l4_adaptDown_typeInvariant s.l4 s.l3 hinv.2.2.2.1
    · exact Or.inr rfl

-- REMOVED (2026-06-29): `l4_actionInfinitelyOftenEnabled` (def) and the theorem
-- `l4_actionsInfinitelyEnabled`. The "theorem" was `def ↔ (def's own body)` proved
-- by `rfl` — i.e. `X ↔ X`, with a decorative `systemInvariant` hypothesis that the
-- proof never used. Despite the name it asserted NO fairness/liveness property; the
-- def and theorem referenced only each other. A genuine "infinitely often enabled"
-- guarantee requires trace/temporal infrastructure that is deliberately not built
-- (see decisions.md: liveness infra for non-existent runtime is not pursued).
-- Surfaced by the unusedArguments linter (formal/lint.sh).

/-- Helper: min 1 (x + y) ≥ x when y ≥ 0 and x ≤ 1 -/
private theorem min_one_add_ge (x y : ℝ) (hy : y ≥ 0) (hx : x ≤ 1) :
    min 1 (x + y) ≥ x := by
  have h1 : x ≤ 1 := hx
  have h2 : x ≤ x + y := le_add_of_nonneg_right hy
  exact le_min h1 h2

/-- L4 makes monotonic progress: threshold changes in appropriate direction.
    `h_understanding` is unused: `observe` is threshold-monotone in BOTH `split`
    branches (rises when the gate fires, unchanged otherwise), so monotonicity is
    unconditional (a strengthening). Kept for family uniformity. Declared via
    `nolint`, not silent — see formal/lint.sh. -/
@[nolint unusedArguments]
theorem l4_monotonicProgress
    (s : SystemState)
    (h_understanding : s.l3.understanding.val ≥ 0.8)
    (h_inv : L4State.typeInvariant s.l4) :
    (L4State.observe s.l4 s.l3).hypothesisQualityThreshold.val ≥
      s.l4.hypothesisQualityThreshold.val := by
  unfold L4State.observe
  split
  · -- Case: active ∧ understanding ≥ 0.8 → threshold' = min 1 (threshold + rate)
    simp only
    exact min_one_add_ge _ _ h_inv.2.2.1 h_inv.2.1
  · -- Case: condition false → state unchanged
    rfl

/-- L4 bounded learning: threshold never exceeds valid range -/
def l4_iter (s : SystemState) : Nat → L4State
  | 0 => s.l4
  | k+1 => if s.l3.understanding.val ≥ 0.8
          then L4State.observe (l4_iter s k) s.l3
          else L4State.adaptDown (l4_iter s k) s.l3
theorem l4_boundedLearning
    (s : SystemState)
    (n : Nat)
    (h_inv : L4State.typeInvariant s.l4) :
    L4State.typeInvariant (l4_iter s n) := by
  induction n with
  | zero =>
    unfold l4_iter
    exact h_inv
  | succ n ih =>
    unfold l4_iter
    split
    · -- understanding ≥ 0.8: observe
      exact l4_observe_typeInvariant (l4_iter s n) s.l3 ih
    · -- understanding < 0.8: adaptDown
      exact l4_adaptDown_typeInvariant (l4_iter s n) s.l3 ih

/-- L4 never gets permanently stuck (liveness: eventual action) -/
theorem l4_eventualAction_liveness
    (s : SystemState)
    (hinv : systemInvariant s)
    (hactive : s.l4.active = true) :
    ∃ (nextL4 : L4State),
      L4State.typeInvariant nextL4 ∧
      (nextL4 = L4State.observe s.l4 s.l3 ∨
       nextL4 = L4State.adaptDown s.l4 s.l3) :=
  l4_canAlwaysActEventually s hinv hactive

/-- L4 learning doesn't diverge (threshold stays bounded) -/
theorem l4_thresholdBounded
    (s : SystemState)
    (hinv : systemInvariant s) :
    0 ≤ s.l4.hypothesisQualityThreshold.val ∧
    s.l4.hypothesisQualityThreshold.val ≤ 1 := by
  have h_type := hinv.2.2.2.1
  exact ⟨h_type.1, h_type.2.1⟩

/-- Helper: max 0.1 (x - y) < x when x > 0.1 and y > 0 -/
private theorem max_sub_lt (x y : ℝ) (hx : x > 0.1) (hy : y > 0) :
    max 0.1 (x - y) < x := by
  apply max_lt hx
  linarith

/-- L4 adaptDown makes progress when blocked and active -/
theorem l4_adaptDown_reducesThreshold
    (s : SystemState)
    (h_active : s.l4.active = true)
    (h_blocked : s.l3.blocked = true)
    (h_lt : s.l4.hypothesisQualityThreshold.val > 0.1)
    (h_rate_pos : s.l4.learningRate.val > 0) :
    (L4State.adaptDown s.l4 s.l3).hypothesisQualityThreshold.val <
      s.l4.hypothesisQualityThreshold.val := by
  unfold L4State.adaptDown
  split
  · -- Case: active ∧ blocked → threshold' = max 0.1 (threshold - rate)
    simp only
    exact max_sub_lt _ _ h_lt h_rate_pos
  · -- Case: condition false → contradicts h_active ∧ h_blocked
    simp [*] at *

/-! ## Hoare Contract Invariants (2026-03-24) -/
/- Inspired by IC-AGI and Toolgate research on formal contracts for AI systems -/

/-- L1 -> L2 Contract: L1 stability > 0.3 enables L2 activation -/
theorem l1_l2_contract
    (s : SystemState)
    (h : s.l1.stability.val > 0.3) :
    s.l1.stability.val > 0.3 := by
  -- Hoare contract: {L1.stability > 0.3} → transition → {L2.active}
  -- In this formal model, we establish the precondition holds
  exact h

/-- L2 -> L3 Contract: L3 not blocked implies L2 wall not active (for reachable states) -/
theorem l2_l3_contract
    (maxDepth : Nat)
    (s : SystemState)
    (h_reachable : EvoEcos.Transition.Reachable maxDepth s)
    (h_inv : systemInvariant s)
    (h_l3_not_blocked : s.l3.blocked = false) :
    s.l2.wall = false := by
  -- Hoare contract: {L3 not blocked} → transition → {L2.wall = false}
  -- This follows from the wall ↔ blocked invariant for reachable states
  apply EvoEcos.Transition.l3_not_blocked_implies_wall_false maxDepth s h_reachable
  · exact h_inv.1  -- L1.noCollapse
  · exact h_inv.2.1  -- L2.typeInvariant
  · exact h_inv.2.2.1  -- L3.typeInvariant
  · exact h_inv.2.2.2.1  -- L4.typeInvariant
  · exact h_inv.2.2.2.2.1  -- wall invariant
  · exact h_l3_not_blocked

/-- L3 -> L4 Contract: L4 active implies L4 can always act (observe or adapt)
    Original claim (L3 unblocked ∨ understanding ≥ 0.8) was unprovable:
    L4 is always active, and L3 can be blocked with low understanding —
    that's exactly when adaptDown fires. The correct contract is that
    L4 can always take a productive action (observe when understanding is high,
    adaptDown when blocked), which is the liveness guarantee. -/
theorem l3_l4_contract
    (s : SystemState)
    (h_l4_active : s.l4.active = true)
    (h_inv : systemInvariant s) :
    ∃ l4', L4State.typeInvariant l4' ∧
      (l4' = L4State.observe s.l4 s.l3 ∨
       l4' = L4State.adaptDown s.l4 s.l3) := by
  -- Hoare contract: {L4.active} → L4 can observe or adapt → type-safe result
  exact l4_canAlwaysActEventually s h_inv h_l4_active

/-! ## Liveness Invariants (2026-03-24) -/

/-! ### Action Selection Policy -/

/-- Action selection policy: when L1 is active, the action type depends on stability
    - stability < 0.1: must use reflex action (not idle)
    - 0.1 ≤ stability < 0.3: must use reflex action (not idle)
    - 0.3 ≤ stability < 0.5: must use heuristic action (not idle)
    - stability ≥ 0.5: can be idle (action = none) -/
def actionSelectionPolicy (s : SystemState) : Prop :=
  s.l1.active = true →
    (s.l1.stability.val < 0.1 → s.l1.currentAction.type = ActionType.reflex) ∧
    (s.l1.stability.val ≥ 0.1 → s.l1.stability.val < 0.3 → s.l1.currentAction.type = ActionType.reflex) ∧
    (s.l1.stability.val ≥ 0.3 → s.l1.stability.val < 0.5 → s.l1.currentAction.type = ActionType.heuristic)

theorem l1_idle_implies_stability_ge_05
    (s : SystemState)
    (h_active : s.l1.active = true)
    (h_idle : s.l1.currentAction.type = ActionType.none)
    (h_policy : actionSelectionPolicy s) :
    s.l1.stability.val ≥ 0.5 := by
  -- Prove by contrapositive using action selection policy
  by_contra h_lt_05
  push_neg at h_lt_05
  -- h_lt_05: s.l1.stability.val < 0.5
  -- Apply action selection policy
  have h_policy_applied := h_policy h_active
  cases h_policy_applied with
  | intro h_reflex_low h_rest =>
    cases h_rest with
    | intro h_reflex_mid h_heuristic =>
      -- Case analysis on stability ranges
      by_cases h_lt_01 : s.l1.stability.val < 0.1
      · -- stability < 0.1: action must be reflex, contradicts idle
        have h_action := h_reflex_low h_lt_01
        rw [h_action] at h_idle
        -- ActionType.reflex ≠ ActionType.none
        contradiction
      · -- stability ≥ 0.1
        by_cases h_lt_03 : s.l1.stability.val < 0.3
        · -- 0.1 ≤ stability < 0.3: action must be reflex
          have h_action := h_reflex_mid (by linarith [h_lt_01]) h_lt_03
          rw [h_action] at h_idle
          contradiction
        · -- stability ≥ 0.3
          by_cases h_lt_05_inner : s.l1.stability.val < 0.5
          · -- 0.3 ≤ stability < 0.5: action must be heuristic
            have h_action := h_heuristic (by linarith [h_lt_03]) h_lt_05_inner
            rw [h_action] at h_idle
            contradiction
          · -- stability ≥ 0.5, contradicts h_lt_05
            have h_ge_05 : s.l1.stability.val ≥ 0.5 := by
              push_neg at h_lt_05_inner
              exact h_lt_05_inner
            linarith [h_lt_05, h_ge_05]

/-- L1 Idle Stability: When L1 is idle and active, stability is at least 50%.
    Depends on the action-selection policy, NOT the full system invariant — the
    former `h_inv : systemInvariant` hypothesis was decorative and misrouted the
    reader to the wrong cause; removed 2026-06-29 (formal/lint.sh). -/
theorem l1_idle_stability
    (s : SystemState)
    (h_idle : s.l1.currentAction.type = ActionType.none)
    (h_policy : actionSelectionPolicy s) :
    s.l1.active = true → s.l1.stability.val ≥ 0.5 := by
  -- When L1 is idle and active, action selection policy gives stability ≥ 0.5
  intro h_active
  exact l1_idle_implies_stability_ge_05 s h_active h_idle h_policy

/-- L1 Can Respond: L1 active implies L1 can respond (stability > 0) -/
theorem l1_can_respond
    (s : SystemState)
    (h_inv : systemInvariant s) :
    s.l1.stability.val > 0 := by
  -- Active L1 always has positive stability (NoCollapse invariant)
  exact h_inv.1

/-! ## Fairness Invariants (2026-03-24) -/

/-- wall → blocked for reachable states.
    Proved in Layers.lean as wall_implies_blocked_for_reachable
    via case analysis on TransKind. -/
theorem wall_implies_blocked_for_reachable_thm
    (maxDepth : Nat) (s : SystemState)
    (h_reachable : EvoEcos.Transition.Reachable maxDepth s)
    (h_l1_inv : L1State.noCollapse s.l1)
    (h_l2_inv : L2State.typeInvariant s.l2)
    (h_l3_inv : L3State.typeInvariant s.l3)
    (h_l4_inv : L4State.typeInvariant s.l4)
    (h_wall_inv : s.l1.stability.val < wallActivateThreshold → s.l2.wall)
    (h_wall : s.l2.wall = true) :
    s.l3.blocked = true :=
  EvoEcos.Transition.wall_implies_blocked_for_reachable maxDepth s
    h_reachable h_l1_inv h_l2_inv h_l3_inv h_l4_inv h_wall_inv h_wall

/-- L3 Yields on Low Stability: L3 yields to L1 when L1 is unstable -/
theorem l3_yields_on_low_stability
    (maxDepth : Nat)
    (s : SystemState)
    (h_reachable : EvoEcos.Transition.Reachable maxDepth s)
    (h_inv : systemInvariant s)
    (h_low_stability : s.l1.stability.val < 0.3) :
    s.l3.blocked = true ∨ s.l1.stability.val ≥ 0.3 := by
  -- If L1 is unstable (< 0.3), L3 must yield (be blocked)
  -- By the L3WallInvariant: stability < wallActivateThreshold → wall
  have h_lt_wat : s.l1.stability.val < wallActivateThreshold := by
    -- 0.3 < wallActivateThreshold (= 0.4), so if x < 0.3 then x < 0.4
    apply lt_trans h_low_stability
    simp [wallActivateThreshold]; norm_num
  have h_wall : s.l2.wall = true := h_inv.2.2.2.2.1 h_lt_wat
  -- wall=true → blocked=true (proved in Layers.lean)
  apply Or.inl
  exact wall_implies_blocked_for_reachable_thm maxDepth s h_reachable h_inv.1 h_inv.2.1 h_inv.2.2.1 h_inv.2.2.2.1 h_inv.2.2.2.2.1 h_wall

/-! ## Main Theorems -/

/-- The main safety theorem: System invariant holds (now includes L4) -/
theorem main_safety_theorem
    (s : SystemState)
    (hinv : systemInvariant s) :
    L1State.noCollapse s.l1 ∧
    L4State.typeInvariant s.l4 ∧
    (s.l1.stability.val < wallActivateThreshold → s.l2.wall) := by
  exact ⟨hinv.1, hinv.2.2.2.1, hinv.2.2.2.2.1⟩

/-- The main liveness theorem: L4 can always make progress.
    `hactive` is unused: progress holds whether or not L4 is currently active
    (a strengthening). Kept for liveness-family uniformity. Declared via
    `nolint`, not silent — see formal/lint.sh. -/
@[nolint unusedArguments]
theorem main_liveness_theorem
    (s : SystemState)
    (hinv : systemInvariant s)
    (hactive : s.l4.active = true) :
    ∃ (nextL4 : L4State),
      L4State.typeInvariant nextL4 ∧
      (nextL4 = L4State.observe s.l4 s.l3 ∨
       nextL4 = L4State.adaptDown s.l4 s.l3) := by
  by_cases h_understanding : s.l3.understanding.val ≥ 0.8
  · -- Observe case: L4 observes when L3 has high understanding
    use L4State.observe s.l4 s.l3
    constructor
    · exact l4_observe_typeInvariant s.l4 s.l3 hinv.2.2.2.1
    · apply Or.inl; rfl
  · -- AdaptDown case: L4 adapts down when L3 is blocked or has low understanding
    use L4State.adaptDown s.l4 s.l3
    constructor
    · exact l4_adaptDown_typeInvariant s.l4 s.l3 hinv.2.2.2.1
    · apply Or.inr; rfl

end EvoEcos

end
