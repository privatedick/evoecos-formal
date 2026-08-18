/-
Code Observation as Non-Injective Projection
=============================================

Source-code reading is a non-injective projection of runtime behavior.
Multiple runtime states (different memory layouts, timing, thread
interleaving) map to the same source code observation. By ACD, there
exist runtime predicates not verifiable from source alone.

Connection to Mythos-class models and Project Glasswing:
  Models that observe source code operate through sourceObs.
  Their cyber capability is bounded by the architectural predicates
  of this observation function. Runtime-dependent bugs (race conditions,
  timing attacks, hardware-state-dependent logic) are counterfactual
  w.r.t. sourceObs and therefore resist source-level discovery.

Results (0 sorry):
  1. source_obs_noninjective — source observation is non-injective
  2. code_analysis_counterfactual_exists — ∃ unverifiable runtime predicates
  3. memory_dependent_counterfactual — memory-dependent predicates are counterfactual
  4. timing_dependent_counterfactual — timing-dependent predicates are counterfactual
  5. race_condition_counterfactual — interleaving-dependent predicates are counterfactual
  6. static_analysis_boundary — architectural predicates are exactly source-determined
-/

import EvoEcos.ACD

namespace EvoEcos

open ObservationalSetup

/-! ## Abstract Types for Code Analysis -/

/-- Source code: what static analysis tools and code-reading models can see. -/
abbrev SourceCode := String

/-- Runtime memory state (abstract hash). Invisible to source-level observation. -/
abbrev MemoryHash := Nat

/-- Execution timing in nanoseconds. Invisible to source-level observation. -/
abbrev TimingNs := Nat

/-- Thread interleaving identifier for concurrent programs.
Invisible to source-level observation. -/
abbrev ThreadId := Nat

/-- Full runtime state: source code + all execution context.
This is the ground truth about a program's execution. -/
abbrev RuntimeState := SourceCode × MemoryHash × TimingNs × ThreadId

/-! ## The Observation Function -/

/-- Source-code observation: projects runtime state to source code.
Discards all execution context — memory, timing, thread interleaving.
This is what static analysis tools, code auditors, and Mythos-class
models can see. -/
def sourceObs (rs : RuntimeState) : SourceCode := rs.1

/-! ## Non-Injectivity -/

/-- Source observation is non-injective: the same source code
corresponds to infinitely many runtime states (different memory,
timing, thread interleaving). -/
theorem source_obs_noninjective : ¬ Function.Injective sourceObs := by
  intro h
  have h1 := @h ("x := 1", 0, 0, 0) ("x := 1", 1, 0, 0) rfl
  have h2 : (0 : Nat) = 1 := congrArg (fun r => r.2.1) h1
  exact Nat.noConfusion h2

/-! ## ACD Applied to Code Analysis -/

/-- The observational setup for code analysis:
worlds are runtime states, observations are source code. -/
def codeAnalysisSetup (truth : RuntimeState → Bool) : ObservationalSetup RuntimeState SourceCode where
  obs := sourceObs
  truth := truth

/-- By ACD, non-injective source observation guarantees the existence
of runtime predicates not verifiable from source code alone. -/
theorem code_analysis_counterfactual_exists :
    ∃ (truth : RuntimeState → Bool),
      ¬ ∀ w1 w2, sourceObs w1 = sourceObs w2 → truth w1 = truth w2 := by
  have h := source_obs_noninjective
  rw [Function.Injective] at h
  push_neg at h
  obtain ⟨a, b, h_obs, h_ne⟩ := h
  classical
  refine ⟨fun w => if w = a then true else false, ?_⟩
  intro hArch
  have h1 := hArch a b h_obs
  simp only [ite_true, ite_false, h_ne.symm] at h1
  nomatch h1

/-! ## Specific Counterfactual Witnesses -/

/-- Memory-dependent predicate: does the runtime memory state
match a target value? Counterfactual because same source can
produce different memory layouts. -/
def memoryPredicate (target : MemoryHash) (w : RuntimeState) : Bool :=
  w.2.1 == target

/-- Memory-dependent predicates are counterfactual w.r.t. source
observation. -/
theorem memory_dependent_counterfactual :
    (codeAnalysisSetup (memoryPredicate 0)).Counterfactual := by
  refine ⟨("x := 1", 0, 0, 0), ("x := 1", 1, 0, 0), rfl, ?_⟩
  decide

/-- Timing-dependent predicate: does execution time exceed
a threshold? -/
def timingPredicate (threshold : Nat) (w : RuntimeState) : Bool :=
  if w.2.2.1 > threshold then true else false

/-- Timing-dependent predicates are counterfactual w.r.t. source
observation. -/
theorem timing_dependent_counterfactual :
    (codeAnalysisSetup (timingPredicate 5)).Counterfactual := by
  refine ⟨("x := 1", 0, 10, 0), ("x := 1", 0, 0, 0), rfl, ?_⟩
  decide

/-- Thread-interleaving predicate: is a specific thread executing?
Race conditions depend on thread interleaving, which is invisible
to source-level observation. -/
def threadPredicate (target : ThreadId) (w : RuntimeState) : Bool :=
  w.2.2.2 == target

/-- Thread-interleaving (race condition) predicates are
counterfactual w.r.t. source observation. -/
theorem race_condition_counterfactual :
    (codeAnalysisSetup (threadPredicate 0)).Counterfactual := by
  refine ⟨("x := 1", 0, 0, 0), ("x := 1", 0, 0, 1), rfl, ?_⟩
  decide

/-! ## The Static Analysis Boundary -/

/-- A runtime predicate is architectural (source-determined) iff
it factors through sourceObs: there exists a source-level function
that agrees with the predicate on all runtime states.

This characterizes exactly what static analysis can and cannot verify:
- Architectural: determined by source code alone (verifiable)
- Counterfactual: depends on runtime state beyond source -/
theorem static_analysis_boundary (truth : RuntimeState → Bool) :
    (codeAnalysisSetup truth).Architectural ↔
    ∃ (f : SourceCode → Bool), ∀ w, truth w = f (sourceObs w) := by
  constructor
  · intro hArch
    classical
    refine ⟨fun s => truth (s, 0, 0, 0), ?_⟩
    intro w
    exact hArch w (w.1, 0, 0, 0) rfl
  · intro ⟨f, hf⟩ w1 w2 hobs
    show truth w1 = truth w2
    rw [hf w1, hf w2]
    exact congrArg f hobs

end EvoEcos
