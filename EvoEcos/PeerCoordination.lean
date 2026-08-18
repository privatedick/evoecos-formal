/-
EvoEcos Peer Coordination Module
==================================

Formal proofs for the Parent-Mediated Peer Coordination (PMPC) protocol.

Architecture:
  PMPC enables sibling EvoEcos instances to share beliefs horizontally
  through their common parent L5, never directly peer-to-peer.

Key Properties Proven:
  1. kill_switch_exclusive      - routing and kill switch are mutually exclusive
  2. ingest_preserves_bounded   - peer belief integration keeps L2 uncertainty in [0,1]
  3. ingest_preserves_wall      - peer belief integration does not change the L3 wall
  4. ingest_type_invariant      - applyPeerBelief preserves L2 type invariant
  5. route_requires_all_healthy - route success implies all three L1s ≥ threshold
  6. ingest_bounded_change      - peer belief changes uncertainty by at most 0.1 (C8 strengthened)

TLA+ Mapping (scaled by 10):
  Python: l1_stability float (0-1)   -> TLA+: L1Values {0,3,5,8,10}
  Python: l2_uncertainty float (0-1) -> TLA+: l2_uncertainty 0..MaxUncertainty
  Python: DELEGATION_THRESHOLD 0.3   -> TLA+: DelegationThreshold 3
-/

import EvoEcos.Layers
import EvoEcos.Hierarchy

noncomputable section

namespace EvoEcos

/-! ## PMPC Constants -/

/-- Wall threshold: L2 wall activates when L1 < this -/
def wallThreshold : ℝ := 0.4

/-! ## Kill Switch Definitions -/

/-- Channel-open predicate: all three L1s meet the delegation threshold.
    This is a COMPUTED predicate (not stored state), matching Python's
    route_sibling_message() which checks all three L1s on each call. -/
def channelOpen (senderL1 receiverL1 parentL1 : Probability) : Prop :=
  senderL1.val ≥ delegationThreshold ∧
  receiverL1.val ≥ delegationThreshold ∧
  parentL1.val ≥ delegationThreshold

/-- Kill switch condition: at least one L1 is below threshold -/
def killSwitchFires (senderL1 receiverL1 parentL1 : Probability) : Prop :=
  senderL1.val < delegationThreshold ∨
  receiverL1.val < delegationThreshold ∨
  parentL1.val < delegationThreshold

/-! ## PMPC Message Types -/

/-- Peer message types (PEER_L2_ONLY_INV: beliefs only, no commands) -/
inductive PeerMessageType where
  | beliefShare    : PeerMessageType
  | knowledgeQuery : PeerMessageType
  | healthReport   : PeerMessageType
deriving Repr, DecidableEq

/-- A peer routing action: sender sends a belief to receiver via parent.
    The `bounded` field (|delta| ≤ 0.1) is load-bearing: `ingest_bounded_change`
    proves that uncertainty changes by at most 0.1, using this bound.
    Safety also comes from `max 0 (min 1 ...)` clamping (keeping values in [0,1]),
    but the delta bound gives the tighter ±0.1 change guarantee. -/
structure PeerRouteAction where
  msgType   : PeerMessageType
  delta     : ℝ          -- uncertainty delta for beliefShare
  bounded   : |delta| ≤ 0.1  -- bounded delta (TLA+: MaxDelta = 1/10)

/-! ## Peer Belief Integration -/

/-- Apply a peer belief to L2 uncertainty (bounded delta update).
    PEER_INDEPENDENCE_INV: takes L2State, returns L2State — L1 not touched. -/
def applyPeerBelief (l2 : L2State) (action : PeerRouteAction) : L2State :=
  if action.msgType = PeerMessageType.beliefShare then
    let new_val := max 0 (min 1 (l2.uncertainty.val + action.delta))
    { l2 with uncertainty := ⟨new_val, by
        constructor
        · exact le_max_left 0 _
        · exact max_le (by norm_num) (min_le_left 1 _)⟩ }
  else
    l2  -- knowledge_query and health_report do not modify L2 uncertainty

/-! ## Key Theorems -/

/-- Theorem: kill_switch_exclusive
    Channel-open and kill-switch-fires are mutually exclusive.
    PEER_KILL_SWITCH_INV: routing is impossible when kill switch would fire. -/
theorem kill_switch_exclusive
    (senderL1 receiverL1 parentL1 : Probability) :
    ¬(channelOpen senderL1 receiverL1 parentL1 ∧
      killSwitchFires senderL1 receiverL1 parentL1) := by
  intro ⟨⟨hs, hr, hp⟩, hk⟩
  rcases hk with h | h | h
  · linarith
  · linarith
  · linarith

/-- Theorem: route_requires_all_healthy
    If routing can proceed (channel open), all three L1s are ≥ threshold.
    Note (C7): This is definitionally true (channelOpen IS the conjunction).
    Kept as documentation that the kill switch check is the sole routing guard. -/
theorem route_requires_all_healthy
    (senderL1 receiverL1 parentL1 : Probability)
    (h : channelOpen senderL1 receiverL1 parentL1) :
    senderL1.val ≥ delegationThreshold ∧
    receiverL1.val ≥ delegationThreshold ∧
    parentL1.val ≥ delegationThreshold := h

/-- Theorem: ingest_preserves_bounded
    Bounded delta update keeps l2_uncertainty within [0, 1]. -/
theorem ingest_preserves_bounded (l2 : L2State) (action : PeerRouteAction) :
    L2State.typeInvariant (applyPeerBelief l2 action) := by
  unfold L2State.typeInvariant applyPeerBelief
  split
  · constructor
    · exact le_max_left 0 _
    · exact max_le (by norm_num) (min_le_left 1 _)
  · exact l2.uncertainty.property

/-- Theorem: ingest_preserves_wall
    Peer belief integration does NOT modify the L3 wall.
    This ensures the wall invariant (L3WallInvariant) is unaffected by PMPC. -/
theorem ingest_preserves_wall (l2 : L2State) (action : PeerRouteAction) :
    (applyPeerBelief l2 action).wall = l2.wall := by
  simp only [applyPeerBelief]
  split <;> rfl

/-- Theorem: ingest_type_invariant
    applyPeerBelief preserves L2 type invariant (regardless of prior state). -/
theorem ingest_type_invariant
    (l2 : L2State)
    (_h : L2State.typeInvariant l2)
    (action : PeerRouteAction) :
    L2State.typeInvariant (applyPeerBelief l2 action) :=
  ingest_preserves_bounded l2 action

/-! ## C8 Strengthening: Delta Bound Is Load-Bearing -/

/-- Helper: clamping (u + d) to [0,1] changes u by at most |d|, when u ∈ [0,1]. -/
private theorem clamp_change_bounded (u d : ℝ)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hd : |d| ≤ 0.1) :
    |max 0 (min 1 (u + d)) - u| ≤ 0.1 := by
  obtain ⟨hd_lo, hd_hi⟩ := abs_le.mp hd
  rw [abs_le]
  constructor
  · -- lower: u - 0.1 ≤ max 0 (min 1 (u + d))
    have h_split := lt_or_ge 0 (u + d)
    rcases h_split with h | h
    · -- 0 < u + d: check if u + d > 1 or ≤ 1
      have h_split2 := lt_or_ge 1 (u + d)
      rcases h_split2 with h2 | h2
      · -- u+d > 1: clamp = 1
        have : max 0 (min 1 (u + d)) = 1 := by
          rw [min_eq_left (le_of_lt h2)]; norm_num
        linarith
      · -- 0 < u+d ≤ 1: clamp = u+d
        have : max 0 (min 1 (u + d)) = u + d := by
          rw [min_eq_right h2]; exact max_eq_right (le_of_lt h)
        linarith
    · -- u + d ≤ 0: clamp ≥ 0 and u ≤ 0.1
      linarith [le_max_left 0 (min 1 (u + d))]
  · -- upper: max 0 (min 1 (u + d)) ≤ u + 0.1
    linarith [max_le (show (0 : ℝ) ≤ u + 0.1 by linarith)
              (le_trans (min_le_right 1 (u + d)) (show u + d ≤ u + 0.1 by linarith))]

/-- Theorem: ingest_bounded_change
    Peer belief integration changes L2 uncertainty by at most 0.1.
    This strengthens C8: the bounded field (|delta| ≤ 0.1) IS load-bearing —
    it guarantees a tighter bound than just [0,1] clamping. -/
theorem ingest_bounded_change (l2 : L2State) (action : PeerRouteAction) :
    |(applyPeerBelief l2 action).uncertainty.val - l2.uncertainty.val| ≤ 0.1 := by
  unfold applyPeerBelief
  split
  · -- beliefShare: uncertainty changes by clamped delta
    exact clamp_change_bounded l2.uncertainty.val action.delta
      l2.uncertainty.property.1 l2.uncertainty.property.2 action.bounded
  · -- non-beliefShare: identity, change = 0
    simp [sub_self]; norm_num

/-- Theorem: wall_invariant_preserved_by_pmpc
    If the wall invariant holds before PMPC ingest, it holds after.
    The wall activates when L1 < 0.4; PMPC does not modify L1.
    Therefore the precondition for wall activation is unchanged. -/
theorem wall_invariant_preserved_by_pmpc
    (l1 : L1State) (l2 : L2State) (action : PeerRouteAction)
    (h_wall : l1.stability.val < wallThreshold → l2.wall = true) :
    l1.stability.val < wallThreshold → (applyPeerBelief l2 action).wall = true := by
  intro h_lt
  rw [ingest_preserves_wall]
  exact h_wall h_lt

/-- Theorem: non_command_ingest_is_identity
    health_report and knowledge_query messages do not modify L2 state. -/
theorem non_command_ingest_is_identity
    (l2 : L2State)
    (action : PeerRouteAction)
    (h : action.msgType ≠ PeerMessageType.beliefShare) :
    applyPeerBelief l2 action = l2 := by
  simp only [applyPeerBelief]
  split
  · next heq => exact absurd heq h
  · rfl

end EvoEcos

end
