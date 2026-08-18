import EvoEcos.ACD

/-!
# The Thermostat Setpoint is Counterfactual (ACD(ii))

**Date:** 2026-07-07

## Statement

A "neural thermostat" — a closed-loop controller that drives the system toward
an *optimal* reference setpoint (e.g. a "productive level of existential
tension") — cannot verify its own reference from the architectural signal
alone. The optimal setpoint is an ACD(ii) quantity: two worlds can share the
same L1-stability observation yet disagree on which setpoint is optimal,
because "what is productive" depends on a counterfactual model (a judgment
about what the system *should* be), not on the observable state.

This formalises the critique that the thermostat frame smuggles a values
question (what state should a person be in?) into an engineering problem
(what is the setpoint?). The wall's L1-stability threshold, by contrast, is
ACD(i): it is `1/(1+reward_variance)`, an observable, and its verifiability
is `architectural_verifiable`.

## Relation to existing results

* `acd_theorem` [CONFIRMED] — the dichotomy this instantiates.
* `beta_observable` [RETIRED] — β (performance ratio) is ACD(ii); the
  thermostat setpoint is the same structural failure applied to a *control
  reference*. β is a performance measure (how good was the outcome); the
  setpoint is a closed-loop reference (what state should we drive toward).
  Different functional role, same unverifiability: both require counterfactual
  access to define.
* `wall_override_defense_hierarchy` / `stackelberg_commitment` [CONFIRMED] —
  those show a non-zero override budget is *exploitable* (a Stackelberg
  failure). This result is orthogonal and stronger-in-form: the setpoint is
  not merely risky to act on, it is *not recoverable* from the architectural
  signal by any estimator, however unbounded. The wall's defense is that it
  acts on an ACD(i) threshold; the thermostat cannot defend acting on an
  ACD(ii) reference at all, because the reference itself is unverifiable.
* `substrate_independence` [NEGATIVE] — the wall's commitment advantage does
  not transfer to graded/rate-based defenses. The thermostat is graded by
  construction (a continuous setpoint), so it sits on the wrong side of that
  scope condition as well.

## What this file proves (0 sorry)

* `thermostatSetup_counterfactual` — the thermostat setup is ACD(ii):
  two worlds with identical L1 signal but different counterfactual
  productivity models share the observation and disagree on the optimal
  setpoint.
* `thermostat_setpoint_unverifiable` — no closed-loop controller reading
  only the L1 signal can be a perfect regulator (recover the optimal
  setpoint). A controller *is* a proactive estimator of the optimal-setpoint
  predicate; by ACD(ii) it cannot be perfect.

## Empirical companion

`src/experiments/experiment_thermostat_setpoint.py` witnesses the
non-identifiability empirically: two designers with different counterfactual
priors (sedation frame vs engagement frame) derive different setpoints from
the *same* L1 signal stream, and no signal-only estimator can recover either
setpoint below the irreducible model gap.
-/

namespace EvoEcos.ThermostatSetpoint

/-! ## The setup -/

/--
A world carries:
* `l1_signal` — the architectural observable (the L1 stability signal,
  `1/(1+reward_variance)`). This is what a proactive controller can see.
* `optimal_high` — whether the *optimal* setpoint is the high-tension one.
  This depends on a counterfactual model of what "productive" means
  (sedation frame → low tension optimal; engagement frame → high tension
  optimal), not on `l1_signal` alone.
-/
structure World where
  l1_signal : ℝ
  optimal_high : Bool

/-- The observation is the L1 signal alone (architectural; the
counterfactual model is discarded by the projection). -/
abbrev obs (w : World) : ℝ := w.l1_signal

/-- Ground truth: "the optimal setpoint is the high-tension one" — the
predicate a thermostat controller must estimate to pick its reference. -/
abbrev truth (w : World) : Bool := w.optimal_high

/-- The thermostat as an `ObservationalSetup`: observe the L1 signal,
estimate the optimal-setpoint predicate. -/
def thermostatSetup : ObservationalSetup World ℝ where
  obs := obs
  truth := truth

/-! ## ACD(ii): the setpoint is counterfactual -/

/--
The thermostat setup is counterfactual: two worlds with the *same* L1
stability signal but *different* counterfactual productivity models
(high-tension-optimal vs low-tension-optimal) share the observation yet
disagree on the optimal setpoint. The setpoint does not factor through the
architectural signal.
-/
theorem thermostatSetup_counterfactual : thermostatSetup.Counterfactual := by
  refine ⟨⟨0.5, true⟩, ⟨0.5, false⟩, rfl, ?_⟩
  intro h
  exact Bool.noConfusion h

/-! ## No perfect regulator -/

/--
**No perfect thermostat regulator.** A closed-loop thermostat controller
reads the L1 observation and decides which setpoint to drive toward; it is a
proactive estimator of the optimal-setpoint predicate. By ACD(ii) it cannot
be perfect: the optimal setpoint is not recoverable from the architectural
signal. Any concrete thermostat must commit to a counterfactual model of
"productive" — its correctness condition is ACD(ii), not ACD(i).

This is the formal statement that the thermostat frame is ill-posed as a
self-verifying closed loop: the wall's L1 threshold (ACD(i)) is verifiable;
the thermostat's setpoint (ACD(ii)) is not. The empirical companion
(`experiment_thermostat_setpoint.py`) witnesses the non-identifiability.
-/
theorem thermostat_setpoint_unverifiable :
    ¬ ∃ f : Estimator ℝ, thermostatSetup.isPerfect f :=
  counterfactual_unverifiable thermostatSetup thermostatSetup_counterfactual

end EvoEcos.ThermostatSetpoint
