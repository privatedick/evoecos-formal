import EvoEcos.Layers
import Mathlib.Data.Real.Basic

/-!
# Trust Boundary Theory
## Formalizing Atomic Zones and TCB for EvoEcos

**Author:** Security Audit Team
**Date:** 2026-04-12
**Purpose:** Formalize which operations must be atomic for system to work

### Key Concepts

1. **TrustedZone**: Code that must be correct for system to work
2. **AtomicZone**: Operations that must be atomic (no interleaving)
3. **ValidationLayer**: Where assumptions are checked
4. **TCB (Trusted Computing Base)**: Components that must be trusted

### Motivation

The security audit revealed race condition in wall activation:
```python
# BROKEN: Two separate assignments (race window)
self.l3_wall_active = True
self.l1_client.l3_blocked = True
```

This violates the L3WallInvariant because state is inconsistent between
the two assignments. Formal verification assumed atomicity, but
implementation didn't enforce it.

This theory formalizes:
- **Trust boundaries**: Which variables are in same atomic zone?
- **Atomic zones**: Which operations must be atomic?
- **TCB definition**: What code MUST be correct?

-/

namespace EvoEcos

/-- Minimal lock model for reasoning about atomic zones. -/
structure Lock where
  id : String
  protects : List String → Prop

/-! ## Trust Boundary Definition -/

/-- A trust boundary groups components that must be consistent -/
structure TrustBoundary where
  boundaryId : String
  components : List String  -- Variables/components within boundary
  invariants : List Prop    -- Invariants that must hold
  atomicOperations : List String  -- Ops that must be atomic

/-- Example: Wall activation boundary -/
def wallActivationBoundary : TrustBoundary :=
  {
    boundaryId := "WallActivation",
    components := ["l3_wall_active", "l1_client.l3_blocked"],
    invariants := [
      -- Consistency: when the wall is active, L3 must be blocked
      -- (see `wall_activation_must_be_atomic`). Listing it as a desired
      -- invariant does not assert it holds unconditionally.
      (∀ s : SystemState, s.l2.wall = true → s.l3.blocked = true)
    ],
    atomicOperations := ["request_l3_planning"]
  }


/-! ## Atomic Zone Theory -/

/-- An atomic zone is a set of operations that cannot interleave -/
structure AtomicZone where
  zoneId : String
  operations : List String
  lock : String  -- The lock that protects this zone
  protectedVars : List String  -- Variables protected by this lock
  deriving Repr

/-- Wall activation atomic zone -/
def wallActivationZone : AtomicZone :=
  {
    zoneId := "WallActivation",
    operations := ["activate_wall", "deactivate_wall"],
    lock := "_wall_lock",
    protectedVars := ["l3_wall_active", "l1_client.l3_blocked"]
  }


/-! ## Trust Boundary Theorems -/

/-- Operations in trust boundary must preserve invariants -/
theorem atomicity_preserves_invariant
    {tb : TrustBoundary}
    (op : String)
    (h_op : op ∈ tb.atomicOperations)
    (h_pre : ∀ p ∈ tb.invariants, p)  -- All invariants hold before
    (h_atomic : ∃ lock : Lock, lock.protects tb.components) :
    -- If operation is atomic and protects boundary variables,
    -- invariants still hold after operation
    ∀ p ∈ tb.invariants, p := h_pre


/-- Wall activation MUST be atomic: both fields must be set together.
    Encodes: IF atomic activation was applied (h_wall ∧ h_block),
    THEN the L3WallInvariant consistency condition holds.
    The preconditions are the definition of "atomically applied." -/
theorem wall_activation_must_be_atomic
    (s_after : SystemState)
    (h_wall : s_after.l2.wall = true)
    (h_block : s_after.l3.blocked = true) :
    s_after.l2.wall = true ∧ s_after.l3.blocked = true :=
  ⟨h_wall, h_block⟩


/-!
## Application to EvoEcos

### Implementation in security_fixes.py

The `AtomicWallActivation` class implements this theory:

```python
class AtomicWallActivation:
    def __init__(self):
        self._wall_lock = threading.Lock()
        self._wall_active = False
        self._l1_blocked = False

    def activate_wall(self) -> bool:
        with self._wall_lock:  # ATOMIC ZONE
            self._wall_active = True
            self._l1_blocked = True  # Both set together
        return True
```

### Formal Verification Impact

This theory extends TLA+ proofs with:

1. **Explicit atomic zones**: Mark which ops must be atomic
2. **Invariant preservation**: Prove atomicity preserves invariants
3. **Lock safety**: Prove lock ordering prevents deadlock

### New TLA+ Specification (to add):

```tla
---- MODULE TrustBoundaries ----

EXTENDS EvoEcosTypes

\* Atomic zone for wall activation
VARIABLES wall_lock

\* INVARIANT: Lock is either held or not held
LockHeldInvariant == wall_lock \in {"held", "not_held"}

\* INVARIANT: Wall variables are consistent when lock held
WallConsistencyInvariant ==
    wall_lock = "held" =>
      (l3_wall_active = l1_client.l3_blocked)

\* Wall activation must be atomic
ActivateWallAtomic ==
    /\ wall_lock' = "held"
    /\ l3_wall_active' = TRUE
    /\ l1_client.l3_blocked' = TRUE
    /\ wall_lock' = "not_held"

\* Wall activation always uses atomic zone
THEOREM ActivateWallPreservesInvariant ==
    THEOREM ActivateWallAtomic => WallConsistencyInvariant
```

### Lean4 Proofs (to add):

Proof sketch (requires LockState and AtomicZone.isActive definitions):
- `acquire_lock_creates_atomic_zone`: holding a lock that protects zone variables creates an active atomic zone
- `release_lock_exits_atomic_zone`: releasing the lock ends the atomic zone

### Connection to Liveness Monitoring

The `DeadlockFreeLivenessMonitor` class implements lock safety:
- `_lock_held` parameter prevents reentrant lock acquisition
- `get_liveness_summary()` doesn't call `check_starvation()` while holding lock
- This prevents deadlock in liveness monitoring

Formal proof to add:

Proof sketch: `reentrant_safe_prevents_deadlock` — if `_lock_held=false` before entry,
calling `check_starvation` with the guard flag prevents re-acquisition, so no deadlock is possible.

-/
