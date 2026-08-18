/-
Kernel.Fleet: ruflo/claude-flow fleet — formalized
===================================================

A second content-bearing instance of the RKS behavioral invariants (peer
to `RKS.ObsLog`), specialized to the ruflo/claude-flow fleet substrate
(ruflo v3.32.8, hierarchical-mesh topology). The State is the fleet event
log — a `List Event` (newest-first, mirroring `RKS.ObsLog`); `update`
prepends. K1 (state preservation) is type-level (total + pure); K2/K3/K4
reduce to list-append mechanics with byte-identical proof skeletons to
`RKS.ObsLog.K2_provenance`, `K3_dependency`, `K4_reproducibility`.

Three event constructors cover the three real fleet mechanics observed in
`.claude-flow/` on 2026-07-19 (cwd `/home/fredde/projects/evoecos`):
  · `Event.spawn aid t`    — `agent_spawn` (new row in `agents/store.json`
    with `agentId = agent-<ms>-<rand>` and one of nine `agentType` values).
  · `Event.emit aid oid`   — agent-emit-output (write to
    `.claude-flow/memory/coordination/*.json`, `/tmp/evoecos-coord/track_*.md`,
    `tasks/store.json` status update, or `memory_store` MCP call).
  · `Event.assign aid tid` — `task_assign` (`assignedTo` field; `[]` in
    every task today).

The fleet-specific contribution is Provenance (`noOrphanOutputs`): every
emitted output must trace to an agent spawned before it. The real fleet
does NOT enforce this today — `.claude-flow/memory/coordination/*.json`
carries no `emitterAgent` field, `tasks/store.json` has `assignedTo = []`
in every task, and `swarm/swarm-state.json` lists `agents: []` in 12 of
13 swarms. Daemon workers (map/audit/optimize/consolidate/testgaps/
backup/harness) have no `AgentID` and are correctly out of model scope —
including them would violate Provenance, which is the correct diagnosis.

The model is NORMATIVE: it prescribes the event-log discipline the fleet
would adopt to become RKS-conformant — tag every emit with its emitter
`AgentID`, route transient routing files (`agent-config.json`,
`routing-decision.json`) through `update`, retain spawn-before-emit
order. See `CLAUDE.md` "Ruflo (claude-flow)" for the operational substrate.
-/

import Kernel.RKS
import Mathlib.Data.Nat.Basic

namespace Kernel.Fleet

/-- Agent identifier: Unix-ms prefix of `agent-<ms>-<rand>` IDs
    (e.g. 1784455999193); for slug IDs (ci-cd-setup, session-investigator)
    use a hash nonce. Models `agents/store.json` keys and gives a total
    spawn order. -/
abbrev AgentID := ℕ

/-- Output identifier: monotone nonce per emitted artifact (one per file
    written to `.claude-flow/memory/coordination/*.json`,
    `/tmp/evoecos-coord/*.md`, `tasks/store.json` update, or `memory_store`
    call). -/
abbrev OutputID := ℕ

/-- Task identifier: Unix-ms prefix of `task-<ms>-<rand>` IDs in
    `tasks/store.json`. -/
abbrev TaskID := ℕ

/-- Exactly the `agentType` values present in `agents/store.json` on
    2026-07-19. -/
inductive AgentType
  | coder | researcher | analyst | coordinator | executor
  | optimizer | planner | scout | general

/-- The three real fleet mechanics: `agent_spawn`, agent-emit-output,
    `task_assign`. -/
inductive Event where
  | spawn : AgentID → AgentType → Event
  | emit : AgentID → OutputID → Event
  | assign : AgentID → TaskID → Event

/-- State: the fleet event log (newest-first, mirroring `RKS.ObsLog`).
    One list, no indexed maps. The log IS the state. -/
abbrev State := List Event

/-- The single fleet transition: prepend an event to the newest-first
    log. Models (a) `agent_spawn` appending a row to `agents/store.json`,
    (b) an agent emitting an output, (c) `task_assign` setting the
    `assignedTo` field. -/
def update (s : State) (e : Event) : State := e :: s

/-! ## Provenance predicates (fleet-specific) -/

/-- Weak membership predicate: the agent was spawned at some point (its
    `agent-<ms>-<rand>` row exists in `agents/store.json`). -/
def spawnedBefore (s : State) (a : AgentID) : Prop :=
  ∃ t : AgentType, Event.spawn a t ∈ s

/-- Stronger temporal helper: there is a list-segment decomposition where
    `spawn a` appears in the `pre` segment (earlier in real time, since
    the log is newest-first) relative to `emit a o`. This is what
    `agent_spawn` preceding any output-write would enforce if the fleet
    maintained an event log. -/
def spawnStrictlyBeforeEmit (s : State) (a : AgentID) (o : OutputID) : Prop :=
  ∃ (pre post : State) (t : AgentType),
    s = post ++ [Event.emit a o] ++ pre ∧ Event.spawn a t ∈ pre

/-! ## Provenance invariant (substantive, fleet-specific) -/

/-- **Provenance (no orphan outputs).** Every emitted output in the log
    traces to an agent that was spawned. The real fleet does NOT enforce
    this today; the invariant is the normative spec the event-log
    discipline would satisfy. -/
def noOrphanOutputs (s : State) : Prop :=
  ∀ (a : AgentID) (o : OutputID), Event.emit a o ∈ s → spawnedBefore s a

/-- Adding a spawn preserves provenance: any emit in the resulting log
    was already in the prior log (spawns and emits are distinct
    constructors, so an emit cannot equal the newly-prepended spawn).
    The witness for the emitter is lifted from `s` via tail-membership. -/
theorem noOrphanOutputs_spawn (s : State) (a : AgentID) (t : AgentType)
    (hs : noOrphanOutputs s) :
    noOrphanOutputs (update s (Event.spawn a t)) := by
  show noOrphanOutputs (Event.spawn a t :: s)
  intro a' o' hmem
  simp only [List.mem_cons] at hmem
  rcases hmem with heq | hpre
  · -- heq : Event.emit a' o' = Event.spawn a t — distinct constructors.
    contradiction
  · -- hpre : Event.emit a' o' ∈ s; lift the spawn-witness from s to the
    -- extended log via tail-membership.
    obtain ⟨t', hm⟩ := hs a' o' hpre
    exact ⟨t', List.mem_cons_of_mem _ hm⟩

/-- Adding an assign preserves provenance (assigns and emits are distinct
    constructors, so an emit cannot equal the newly-prepended assign). -/
theorem noOrphanOutputs_assign (s : State) (a : AgentID) (tid : TaskID)
    (hs : noOrphanOutputs s) :
    noOrphanOutputs (update s (Event.assign a tid)) := by
  show noOrphanOutputs (Event.assign a tid :: s)
  intro a' o' hmem
  simp only [List.mem_cons] at hmem
  rcases hmem with heq | hpre
  · -- heq : Event.emit a' o' = Event.assign a tid — distinct constructors.
    contradiction
  · obtain ⟨t', hm⟩ := hs a' o' hpre
    exact ⟨t', List.mem_cons_of_mem _ hm⟩

/-- Adding an emit `emit a o` preserves provenance WHEN the emitter `a`
    was already spawned in `s`. This is the normative gate the real fleet
    would enforce by tagging each emit with its emitter `AgentID`. -/
theorem noOrphanOutputs_emit (s : State) (a : AgentID) (o : OutputID)
    (hs : noOrphanOutputs s) (hspawn : spawnedBefore s a) :
    noOrphanOutputs (update s (Event.emit a o)) := by
  show noOrphanOutputs (Event.emit a o :: s)
  intro a' o' hmem
  simp only [List.mem_cons] at hmem
  rcases hmem with heq | hpre
  · -- heq : Event.emit a' o' = Event.emit a o — by injectivity, a' = a.
    injection heq with ha ho
    subst ho
    subst ha
    obtain ⟨t', hm⟩ := hspawn
    exact ⟨t', List.mem_cons_of_mem _ hm⟩
  · obtain ⟨t', hm⟩ := hs a' o' hpre
    exact ⟨t', List.mem_cons_of_mem _ hm⟩

/-- **Provenance preservation under `update`.** Unified law: `update`
    preserves `noOrphanOutputs` whenever the appended event is
    well-formed — a spawn or assign is always safe; an emit `emit a o`
    requires `spawnedBefore s a` (the side condition the real fleet would
    enforce by tagging each emit with its emitter `AgentID`).

    This is the closest the model gets to a closed `noOrphanOutputs`
    theorem: the predicate is not closed under arbitrary `update` — an
    emit without a prior spawn would violate it — so the substantive
    statement is the preservation law. -/
theorem noOrphanOutputs_update (s : State) (e : Event)
    (hs : noOrphanOutputs s)
    (he : match e with
          | Event.emit a _ => spawnedBefore s a
          | _ => True) :
    noOrphanOutputs (update s e) := by
  cases e with
  | spawn a t => exact noOrphanOutputs_spawn s a t hs
  | assign a tid => exact noOrphanOutputs_assign s a tid hs
  | emit a o => exact noOrphanOutputs_emit s a o hs he

/- K1 — State Preservation: `update s e : State` is total (type-level). -/

/-- **K2 — Strict Growth.** Each fleet action (spawn, emit, assign)
    strictly extends the event log. Maps to: every `agent_spawn` adds a
    row to `agents/store.json`; every output write adds a file row; every
    `task_assign` adds an entry. The fleet's per-agent `taskCount` (always
    0 in the data) and aggregate `metrics.tasks` counters fail to enforce
    this per-action — they are counters, not a strict-growth log. The
    model prescribes the log discipline that would close the gap. -/
theorem K2_strict_growth (s : State) (e : Event) :
    s.length < (update s e).length := by
  show s.length < (e :: s).length
  rw [List.length_cons]
  exact Nat.lt.base s.length

/-- **K3 — Monotone Extension.** The post-state monotonically extends
    the pre-state: appending an event never shortens the log. Maps to: a
    new spawn/emit/assign never removes or overwrites a prior record.
    The fleet's actual `.claude-flow/agent-config.json` and
    `.claude-flow/routing-decision.json` VIOLATE this — they are
    overwritten each prompt, destroying prior routing history. The model
    prescribes the fix: route those transient files through `update` so
    each routing decision becomes a permanent event. -/
theorem K3_monotone_extension (s : State) (e : Event) :
    s.length ≤ (update s e).length := by
  show s.length ≤ (e :: s).length
  rw [List.length_cons]
  exact Nat.le_succ s.length

/-- **K4 — Reproducibility.** Replaying the same spawn+emit+assign
    sequence from a fixed initial log reconstructs the same final log:
    `foldl update s es = es.reverse ++ s`. The replay order is
    deterministic; the final state is determined by the initial state
    and the sequence. The real fleet does NOT achieve this today (emit
    →agent link missing; routing history overwritten). The theorem holds
    for the abstract model; the real fleet satisfies it only after
    adopting the model's event-log discipline. -/
theorem K4_reproducibility (s : State) (es : List Event) :
    List.foldl update s es = es.reverse ++ s := by
  induction es generalizing s with
  | nil => simp [List.reverse_nil, update]
  | cons e es ih =>
    show List.foldl update (e :: s) es = (e :: es).reverse ++ s
    rw [ih (e :: s), List.reverse_cons, List.append_assoc]
    rfl

end Kernel.Fleet
