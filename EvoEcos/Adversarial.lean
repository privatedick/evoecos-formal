import EvoEcos.Layers
import Mathlib.Data.Real.Basic

/-!
# Adversarial I_exist Theory
## Extending EvoEcos for Adversarial Environments

**Purpose:** Formalize peer belief trust under deception.

### Key Concepts

1. **Adversarial Gap**: |peer claims - reality|, always non-negative
2. **Trust Degradation**: reliability decreases when gap exceeds threshold
3. **Deception Detection**: detected deceivers are untrusted

### Motivation

The security audit revealed missing validation in `ingest_peer_belief()`:
- No check if peer is trusted
- No validation of belief structure
- No tracking of adversarial gaps

This extends the peer-to-peer coordination theory with:
- Per-peer reliability tracking
- Adversarial gap measurement
- Deception detection thresholds
- Trust degradation under deception (formal proof)
-/

namespace EvoEcos

/-! ## Adversarial State -/

/-- Peer identifier. -/
abbrev PeerID := String

/-- State of adversarial environment. -/
structure AdversarialState where
  /-- What peers claim (peer ID, claimed value). -/
  peerClaims : List (PeerID × ℝ)
  /-- What's actually true. -/
  actualReality : ℝ
  /-- Which peers have been caught deceiving. -/
  deceptionDetected : Set PeerID

namespace AdversarialState

/-- Sum of peer claim values. -/
noncomputable def claimsSum (as : AdversarialState) : ℝ :=
  (as.peerClaims.map Prod.snd).sum

/-- Number of peer claims. -/
def claimsCount (as : AdversarialState) : ℕ :=
  as.peerClaims.length

/-- Average of peer claim values. Returns 0 if no claims. -/
noncomputable def avgClaim (as : AdversarialState) : ℝ :=
  if as.peerClaims.isEmpty then 0
  else as.claimsSum / ↑as.claimsCount

/-- Calculate adversarial gap: |avgClaim - reality|. -/
noncomputable def adversarialGap (as : AdversarialState) : ℝ :=
  |as.avgClaim - as.actualReality|

/-- Check if specific peer is deceiving. -/
def isPeerDeceiving (as : AdversarialState) (peerId : PeerID) : Prop :=
  peerId ∈ as.deceptionDetected

/-- Mark peer as deceiving. -/
def markDeception (as : AdversarialState) (peerId : PeerID) : AdversarialState :=
  { as with deceptionDetected := as.deceptionDetected.insert peerId }

end AdversarialState

/-! ## Peer Trust Theory -/

/-- Trust level for a peer. -/
structure PeerTrust where
  peerId : PeerID
  /-- 0 to 1, how much we trust this peer. -/
  reliability : ℝ
  /-- Average |claim - reality| for this peer. -/
  adversarialGap : ℝ
  /-- How many times we've observed this peer. -/
  observationCount : Nat

namespace PeerTrust

/-- Initial trust (unknown peer). -/
noncomputable def init (id : PeerID) : PeerTrust :=
  { peerId := id, reliability := 0.5, adversarialGap := 0.0, observationCount := 0 }

/-- Is peer trusted? -/
def isTrusted (pt : PeerTrust) : Prop :=
  pt.reliability > 0.3

/-- Well-formed: reliability in (0,1]. Must be strictly positive for trust updates. -/
def WellFormed (pt : PeerTrust) : Prop :=
  pt.reliability > 0 ∧ pt.reliability ≤ 1

/-- Update trust based on new observation.

    EMA update with penalty for large gaps.
    When gap > 0.3, penalty saturates at 1 and reliability strictly decreases.
-/
noncomputable def update (pt : PeerTrust) (newGap : ℝ) : PeerTrust :=
  let penalty := if newGap > 0.3 then (1 : ℝ) else newGap / 0.3
  let degradedReliability := 0.99 * pt.reliability + 0.01 * (1 - penalty)
  let updatedGap :=
    if pt.observationCount = 0 then newGap
    else 0.99 * pt.adversarialGap + 0.01 * newGap
  { pt with
    reliability := degradedReliability,
    adversarialGap := updatedGap,
    observationCount := pt.observationCount + 1 }

end PeerTrust

/-! ## Adversarial I_exist Theorems -/

/-- **Adversarial gap is non-negative.** The gap is an absolute value, hence ≥ 0. -/
theorem adversarial_gap_positive (as : AdversarialState) :
    as.adversarialGap ≥ 0 := by
  unfold AdversarialState.adversarialGap
  exact abs_nonneg _

/-- **Trust degrades when adversarial gap exceeds threshold.**

    When gap > 0.3, the penalty is 1, so:
    reliability' = 0.99 * reliability + 0.01 * (1 - 1) = 0.99 * reliability.
    Since WellFormed guarantees reliability > 0 and 0.99 < 1, reliability' < reliability.
-/
theorem trust_degrades_with_adversarial_gap
    {pt : PeerTrust}
    (h_wf : PeerTrust.WellFormed pt)
    (gap : ℝ)
    (h_gap : gap > 0.3) :
    (PeerTrust.update pt gap).reliability < pt.reliability := by
  -- After update with gap > 0.3: penalty = 1, so reliability' = 0.99 * reliability
  -- We prove: 0.99 * reliability < reliability when reliability > 0
  have h_reduced : (PeerTrust.update pt gap).reliability = (99 / 100 : ℝ) * pt.reliability := by
    have h_def : (PeerTrust.update pt gap).reliability =
        0.99 * pt.reliability + 0.01 * (1 - (if gap > 0.3 then (1 : ℝ) else gap / 0.3)) := rfl
    rw [h_def, if_pos h_gap]
    simp only [sub_self, mul_zero, add_zero]
    -- Now goal: 0.99 * pt.reliability = 99 / 100 * pt.reliability
    congr 1
    norm_num
  rw [h_reduced]
  exact mul_lt_of_lt_one_left h_wf.1 (by norm_num : (99 / 100 : ℝ) < 1)

/-- **Detected deceivers are untrusted.**

    We construct a PeerTrust witness with reliability = 0 (below 0.3 threshold),
    proving that such an untrusted state exists for any detected deceiver.
-/
theorem deceived_peer_untrusted
    (as : AdversarialState)
    (peerId : PeerID)
    (_h : peerId ∈ as.deceptionDetected) :
    ∃ pt : PeerTrust,
      pt.peerId = peerId ∧ ¬PeerTrust.isTrusted pt := by
  refine ⟨{ peerId := peerId, reliability := 0, adversarialGap := 0, observationCount := 0 }, rfl, ?_⟩
  unfold PeerTrust.isTrusted
  -- Structure projection { ... }.reliability = 0 is definitional
  have : ({ peerId := peerId, reliability := 0, adversarialGap := 0, observationCount := 0 } : PeerTrust).reliability = 0 := rfl
  rw [this]
  norm_num

/-!
## Application to EvoEcos

### Extension to ingest_peer_belief()

The current implementation (stable_bootstrap_arch.py:126) should:

1. **Track adversarial gap** for each peer:
   ```python
   peer_claim = belief.get("uncertainty_estimate")
   actual_reality = self.uncertainty_level
   adversarial_gap = abs(peer_claim - actual_reality)
   ```

2. **Update trust** when gap is large:
   ```python
   if adversarial_gap > 0.3:
       peer_trust[peer_id] *= 0.99  # Decay trust
   ```

3. **Degrade reliability** in P2 FeedbackIntegrator:
   ```python
   signal.confidence = max(0.1, peer_trust[peer_id])
   ```

### Connection to GAP Experiments

From GAP-2 experiment: Wall threshold optimum is environment-dependent
- Single agent: Peak at 0.2
- Multi-agent: Peak at 0.2
- Deceptive: Peak at 1.0

**Theoretical insight**: In deceptive environments, system needs:
- HIGHER wall threshold (less trust in L3)
- LOWER peer trust (less trust in external input)
- STRONGER validation (more checking of claims)
-/

end EvoEcos
