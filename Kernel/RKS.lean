/-
Kernel.RKS: Reasoning Kernel Specification v0.1 — formalized
=============================================================

The RKS behavioral invariants over the simplest conformant instance: the
counter model (State = ℕ, update = +1). K1 (state preservation) and K4
(reproducibility) are type-level in Lean (total + pure). K2 (provenance)
and K3 (dependency) are proven as strict/monotone growth properties.

The counter model is non-vacuous: the increment IS the provenance trace
(each observation leaves a measurable mark — the state grew). More complex
instances (observation-log, TMS, Bayesian) must satisfy the same K2-K3
invariants in their own representation.
-/

import Mathlib.Data.Nat.Basic

namespace RKS

structure Observation where
  id : ℕ

/-- State: a counter (simplest conformant instance). -/
abbrev State := ℕ

/-- The kernel transition: increment for each observation applied. -/
def update (s : State) (_o : Observation) : State := s + 1

/- K1 — State Preservation: `update s o : ℕ` is total (type-level). -/

/-- **K4 — Reproducibility.** Replaying the same observation sequence from
    the same initial state reconstructs the same final state. For the counter
    model: `foldl update s os = s + os.length` (each observation adds 1). -/
theorem K4_reproducibility (s : State) (os : List Observation) :
    List.foldl update s os = s + os.length := by
  induction os generalizing s with
  | nil => simp [update]
  | cons _ os ih =>
    show List.foldl update (s + 1) os = s + (os.length + 1)
    rw [ih (s + 1), Nat.add_assoc, Nat.add_comm 1]

/-- **K2 — Provenance Preservation.** The post-update state strictly exceeds
    the pre-update — each observation leaves a measurable trace (the increment). -/
theorem K2_provenance (s : State) (o : Observation) :
    s < update s o := Nat.lt.base s

/-- **K3 — Dependency Preservation.** The post-update state depends on
    (monotonically extends) the pre-update state. -/
theorem K3_dependency (s : State) (o : Observation) :
    s ≤ update s o := Nat.le_succ s

end RKS

/-
RKS.ObsLog: the observation-log instance
==========================================

A second conforming instance of the RKS behavioral invariants — distinct
from the counter. Here `State` is the observation log itself (a list of
observations, newest-first), and `update` prepends. The same K2–K4
invariants hold, measured by log length and structural equality rather
than by a counter.

Two distinct instances satisfying the same invariants is what makes RKS a
*specification* rather than a single-model restatement: any conformant
kernel — counter, log, TMS, Bayesian — must satisfy K2–K4 in its own
representation. The counter instance above is the trivial model; this is
the canonical content-bearing one.
-/

namespace RKS.ObsLog

/-- An observation carries an opaque identifier. -/
structure Observation where
  id : ℕ

/-- State: the observation log (newest-first). -/
abbrev State := List Observation

/-- The kernel transition: prepend the observation to the log. -/
def update (s : State) (o : Observation) : State := o :: s

/-- **K2 — Provenance Preservation.** Each update strictly grows the log —
    the observation is recorded (its presence is measurable via length). -/
theorem K2_provenance (s : State) (o : Observation) :
    s.length < (update s o).length := by
  show s.length < (o :: s).length
  rw [List.length_cons]
  exact Nat.lt.base s.length

/-- **K3 — Dependency Preservation.** The post-update log is at least as
    long as the pre-update log (monotone extension). -/
theorem K3_dependency (s : State) (o : Observation) :
    s.length ≤ (update s o).length := by
  show s.length ≤ (o :: s).length
  rw [List.length_cons]
  exact Nat.le_succ s.length

/-- **K4 — Reproducibility.** Replaying an observation sequence from a
    fixed initial log reconstructs the same final log:
    `foldl update s os = os.reverse ++ s`. The replay order is deterministic;
    the final state is determined by the initial state and the sequence. -/
theorem K4_reproducibility (s : State) (os : List Observation) :
    List.foldl update s os = os.reverse ++ s := by
  induction os generalizing s with
  | nil => simp [List.reverse_nil, update]
  | cons o os ih =>
    show List.foldl update (o :: s) os = (o :: os).reverse ++ s
    rw [ih (o :: s), List.reverse_cons, List.append_assoc]
    rfl

end RKS.ObsLog
