import EvoEcos.Layers

/-!
# Alignment Measurement Impossibility
## Observational Underdetermination of Retroactive Outcomes

**Date:** 2026-04-14

### Claim
No proactive measurement function `f : SystemState → Bool` can be correct
on every world, because two worlds can share the same observable
`SystemState` and still yield different retroactive outcomes.

### Why observational equivalence is the right formulation
A proactive measurer, by definition, has access only to the current
observable state. The retroactive outcome depends on information that is
not yet in that state (future interactions, environment perturbations,
consequences of the action itself). If two distinct worlds agree on the
observable present, every measurement function on the present must give
them the same verdict, even though their retroactive truths differ. At
least one of the two worlds must therefore be misjudged.

This is the standard structure of no-go results that rest on
underdetermination (latent-variable identifiability, hidden-state control).
It is isomorphic to the beta-as-observable retirement in HI2 and the
I_exist measurement gap in the C1 draft: in all three cases a quantity
that depends on counterfactual futures cannot be read off the observable
present.

### What this file proves (0 sorry)
* `observational_underdetermination` — for every observable state, there
  exist two worlds with that observable and opposite retroactive outcomes.
* `measurement_impossibility` — for every measurement function and every
  observable state, one of those two worlds is misjudged.
* `no_perfect_measurement` — no measurement function is correct on every
  world.
* `adaptive_estimation_necessary` — any measurement function collapses
  some pair of distinct-outcome worlds to the same verdict.
-/

namespace EvoEcos

/-! ## Worlds and Measurement Functions -/

/--
A world pairs an observable present (`SystemState`) with the retroactive
truth about alignment. The retroactive outcome is `true` iff the system
turned out to be aligned after deployment. Two worlds may share
`observable` and disagree on `retroactiveOutcome`; that is the whole
point.
-/
structure AlignmentWorld where
  observable : SystemState
  retroactiveOutcome : Bool

/--
A proactive measurement function consumes only the current observable
state. It returns a verdict (`true` = predicted aligned). The crucial
constraint is the type signature itself: no access to the retroactive
outcome.
-/
abbrev MeasurementFn := SystemState → Bool

/-- `f` is correct on a world iff its verdict matches the retroactive
truth of that world. -/
def correct (f : MeasurementFn) (w : AlignmentWorld) : Prop :=
  f w.observable = w.retroactiveOutcome

/-- `f` is perfect iff it is correct on every world. -/
def isPerfect (f : MeasurementFn) : Prop :=
  ∀ w : AlignmentWorld, correct f w


/-! ## Core Impossibility Results -/

/--
**Observational underdetermination.** For every observable `s`, the pair
`⟨s, true⟩, ⟨s, false⟩` witnesses two worlds that share the same
observable and disagree on retroactive outcome.
-/
theorem observational_underdetermination (s : SystemState) :
    ∃ w1 w2 : AlignmentWorld,
      w1.observable = w2.observable ∧
      w1.retroactiveOutcome ≠ w2.retroactiveOutcome := by
  refine ⟨⟨s, true⟩, ⟨s, false⟩, rfl, ?_⟩
  intro h
  exact Bool.noConfusion h

/--
**Measurement impossibility.** For every measurement function `f` and
every observable `s`, there exist two worlds with observable `s` and
opposite retroactive outcomes such that `f` misjudges at least one of
them.

The proof is case analysis on `f s`: whichever verdict the function
commits to, the world with the opposite retroactive outcome is a
counterexample.
-/
theorem measurement_impossibility (f : MeasurementFn) (s : SystemState) :
    ∃ w1 w2 : AlignmentWorld,
      w1.observable = s ∧
      w2.observable = s ∧
      w1.retroactiveOutcome ≠ w2.retroactiveOutcome ∧
      (¬ correct f w1 ∨ ¬ correct f w2) := by
  refine ⟨⟨s, true⟩, ⟨s, false⟩, rfl, rfl, ?_, ?_⟩
  · intro h; exact Bool.noConfusion h
  · by_cases h : f s = true
    · right
      intro hc
      unfold correct at hc
      -- hc : f s = false but h : f s = true
      rw [h] at hc
      exact Bool.noConfusion hc
    · left
      intro hc
      unfold correct at hc
      -- hc : f s = true, contradicts h
      exact h hc

/--
**No perfect measurement function exists.** Any function claimed to be
correct on every world produces contradictory verdicts on two worlds
that share an observable.
-/
theorem no_perfect_measurement : ¬ ∃ f : MeasurementFn, isPerfect f := by
  rintro ⟨f, hf⟩
  let s : SystemState := SystemState.init 1
  have h1 : f s = true := hf ⟨s, true⟩
  have h2 : f s = false := hf ⟨s, false⟩
  rw [h1] at h2
  exact Bool.noConfusion h2

/--
**Adaptive estimation is necessary.** Any measurement function collapses
some pair of worlds with distinct retroactive outcomes onto the same
verdict. Any strategy that hopes to be right more often must therefore
condition on information beyond the collapsed observable (history,
environment, side-channel evidence) — exactly the adaptive-estimation
corollary that motivates the wall mechanism in L2.
-/
theorem adaptive_estimation_necessary (f : MeasurementFn) :
    ∃ w1 w2 : AlignmentWorld,
      f w1.observable = f w2.observable ∧
      w1.retroactiveOutcome ≠ w2.retroactiveOutcome := by
  let s : SystemState := SystemState.init 1
  refine ⟨⟨s, true⟩, ⟨s, false⟩, rfl, ?_⟩
  intro h
  exact Bool.noConfusion h


/-! ## Connection to EvoEcos Architecture

* L3 proactive alignment checks are instances of `MeasurementFn`: they
  map the current `SystemState` to a verdict. `measurement_impossibility`
  says no such check can be perfect.
* The wall mechanism in L2 is exactly the adaptive-estimation response
  from `adaptive_estimation_necessary`: when the observable is known to
  underdetermine the retroactive outcome (low budget, high stakes,
  deception regime from the context-chain experiments), the system
  must fall back on a structural invariant instead of a verdict.
* This is why surviving findings in the C1 draft are all architectural
  invariants (`L1Independence`, `NoCollapse`, wall activation) rather
  than learned alignment predictors.
-/

end EvoEcos
