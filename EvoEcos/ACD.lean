import EvoEcos.AlignmentImpossibility

/-!
# Architecture-Counterfactual Dichotomy (ACD)

**Date:** 2026-04-14

## Statement

Every predicate on a system's state space falls into exactly one of two
classes relative to an observational interface:

* **Architectural.** Observationally equivalent worlds always share the
  same truth value. Architectural predicates are determined by the
  observation — they lift to a function on observations alone and admit
  a perfect proactive estimator (given realization).

* **Counterfactual.** There exist two observationally equivalent worlds
  with different truth values. Counterfactual predicates are not
  determined by the observation — no proactive estimator can be perfect.

The two classes are mutually exclusive and exhaustive, hence a dichotomy.
This is the structural characterisation underlying EvoEcos's distinction
between formally verifiable safety properties (architectural invariants
like `L1Independence`) and empirically unverifiable measurement targets
(β, alignment, I_exist).

## Generalisation of existing results

`AlignmentImpossibility.lean` proves a specific instance: no measurement
function on `SystemState` can be perfect with respect to retroactive
alignment outcomes. ACD generalises that result to any observational
setup and exhibits alignment impossibility as a corollary.

## What this file proves (0 sorry)

* `architectural_iff_not_counterfactual` — the two classes partition.
* `architectural_verifiable` — ACD(i): architectural ⇒ perfect estimator.
* `counterfactual_unverifiable` — ACD(ii): counterfactual ⇒ no perfect
  estimator.
* `ACD` — the combined dichotomy theorem.
* `alignmentSetup_counterfactual` — alignment is counterfactual.
* `alignment_impossibility_corollary` — alignment impossibility as an
  instance of ACD(ii).
-/

namespace EvoEcos

/-! ## Observational Setup -/

/--
An observational setup packages three things:
* `W` — the space of worlds (full ground truth).
* `O` — the observable interface accessible to a proactive measurer.
* `obs : W → O` — the projection from worlds to observations.
* `truth : W → Bool` — the ground truth predicate to be estimated.

Two worlds `w1 w2 : W` are *observationally equivalent* iff
`obs w1 = obs w2`. A proactive estimator, by definition, can only see
`obs w`, not `w` itself, and therefore cannot distinguish observationally
equivalent worlds.
-/
structure ObservationalSetup (W : Type) (O : Type) where
  obs   : W → O
  truth : W → Bool

/-- A proactive estimator consumes only the observation. -/
abbrev Estimator (O : Type) := O → Bool

namespace ObservationalSetup

variable {W O : Type} (S : ObservationalSetup W O)

/-- `f` is correct on world `w` iff its verdict on the observation of
`w` matches the ground truth of `w`. -/
def correct (f : Estimator O) (w : W) : Prop :=
  f (S.obs w) = S.truth w

/-- `f` is perfect iff it is correct on every world. -/
def isPerfect (f : Estimator O) : Prop :=
  ∀ w : W, S.correct f w

/--
`S` is **architectural** iff observationally equivalent worlds always
agree on truth. Equivalently: `truth` factors through `obs`.
-/
def Architectural : Prop :=
  ∀ w1 w2 : W, S.obs w1 = S.obs w2 → S.truth w1 = S.truth w2

/--
`S` is **counterfactual** iff some pair of observationally equivalent
worlds disagrees on truth. Equivalently: `truth` does not factor
through `obs`.
-/
def Counterfactual : Prop :=
  ∃ w1 w2 : W, S.obs w1 = S.obs w2 ∧ S.truth w1 ≠ S.truth w2

end ObservationalSetup


/-! ## Partition: Architectural ↔ ¬ Counterfactual -/

/--
The architectural and counterfactual classes are exact negations of
each other. A setup is architectural iff it is not counterfactual.
-/
theorem architectural_iff_not_counterfactual {W O : Type}
    (S : ObservationalSetup W O) :
    S.Architectural ↔ ¬ S.Counterfactual := by
  constructor
  · intro hA ⟨w1, w2, hobs, htruth⟩
    exact htruth (hA w1 w2 hobs)
  · intro hNC w1 w2 hobs
    by_contra htruth
    exact hNC ⟨w1, w2, hobs, htruth⟩


/-! ## ACD(i): Architectural ⇒ Verifiable -/

/--
**ACD(i).** If `S` is architectural and every observation is realised
by at least one world, then a perfect proactive estimator exists. It is
constructed by lifting `truth` across the equivalence kernel of `obs`:
pick any witnessing world for each observation and read its truth.

The `realized` hypothesis is essential: without it, the estimator has
no way to produce a verdict for observations that are not instantiated.
In a finite transition system this hypothesis is trivially satisfied by
reachability.
-/
theorem architectural_verifiable {W O : Type} (S : ObservationalSetup W O)
    (hArch : S.Architectural)
    (realized : ∀ o : O, ∃ w : W, S.obs w = o) :
    ∃ f : Estimator O, S.isPerfect f := by
  classical
  refine ⟨fun o => S.truth (Classical.choose (realized o)), ?_⟩
  intro w
  show S.truth (Classical.choose (realized (S.obs w))) = S.truth w
  have hw' : S.obs (Classical.choose (realized (S.obs w))) = S.obs w :=
    Classical.choose_spec (realized (S.obs w))
  exact hArch _ _ hw'


/-! ## ACD(ii): Counterfactual ⇒ Unverifiable -/

/--
**ACD(ii).** If `S` is counterfactual, then no proactive estimator is
perfect. The proof is direct: the two witnessing worlds share an
observation, so any estimator produces the same verdict on both; that
verdict can match at most one of the two distinct truths.
-/
theorem counterfactual_unverifiable {W O : Type} (S : ObservationalSetup W O)
    (hCF : S.Counterfactual) :
    ¬ ∃ f : Estimator O, S.isPerfect f := by
  rintro ⟨f, hf⟩
  obtain ⟨w1, w2, hobs, htruth⟩ := hCF
  have h1 : f (S.obs w1) = S.truth w1 := hf w1
  have h2 : f (S.obs w2) = S.truth w2 := hf w2
  rw [hobs] at h1
  exact htruth (h1.symm.trans h2)


/-! ## The Dichotomy -/

/--
**Architecture-Counterfactual Dichotomy.** For every observational
setup, exactly one of the following holds:
* `S.Architectural` — truth is determined by the observation.
* `S.Counterfactual` — truth depends on information beyond the
  observation.

Combined with ACD(i) and ACD(ii), this partitions all measurement
problems into a verifiable class and an unverifiable class based on a
purely structural criterion.
-/
theorem ACD {W O : Type} (S : ObservationalSetup W O) :
    S.Architectural ∨ S.Counterfactual := by
  rcases Classical.em S.Counterfactual with h | h
  · exact Or.inr h
  · exact Or.inl ((architectural_iff_not_counterfactual S).mpr h)


/-! ## AlignmentImpossibility as a corollary of ACD(ii) -/

/-- The observational setup for alignment: worlds are
`AlignmentWorld`, observations are `SystemState`, and truth is the
retroactive deployment outcome. -/
def alignmentSetup : ObservationalSetup AlignmentWorld SystemState where
  obs   := AlignmentWorld.observable
  truth := AlignmentWorld.retroactiveOutcome

/--
`alignmentSetup` is counterfactual: for any observable `SystemState`,
the worlds `⟨s, true⟩` and `⟨s, false⟩` share the observation but
disagree on the retroactive outcome.
-/
theorem alignmentSetup_counterfactual : alignmentSetup.Counterfactual := by
  refine ⟨⟨SystemState.init 1, true⟩, ⟨SystemState.init 1, false⟩, rfl, ?_⟩
  intro h
  exact Bool.noConfusion h

/--
**Alignment impossibility as a corollary of ACD(ii).** No proactive
alignment measurement function is perfect. This result was proved
directly in `AlignmentImpossibility.lean` as `no_perfect_measurement`;
here it is re-derived as a special case of the general dichotomy,
confirming that alignment unverifiability is not a peculiarity of the
alignment setting but an instance of a structural theorem.
-/
theorem alignment_impossibility_corollary :
    ¬ ∃ f : Estimator SystemState, alignmentSetup.isPerfect f :=
  counterfactual_unverifiable alignmentSetup alignmentSetup_counterfactual


/-! ## Connection to EvoEcos Architecture

The ACD provides a single structural explanation for the EvoEcos C1
paper's §4.2 observation that surviving findings are architectural
invariants and failed findings are counterfactual-dependent measurements.

* `l1Independence` (Lean `Invariants.lean`) is architectural in the sense
  of ACD: it is a predicate on the transition system's edge set
  (specifically, the absence of an L3→L1 bleed edge) and therefore
  factors through any observation that preserves edge structure.
  ACD(i) gives its verifiability.

* The beta-as-observable, LZ/TE proxy, and alignment measurement claims
  are counterfactual: their truth depends on information not present in
  the current observation (optimal policy, transfer entropy across
  unobserved futures, deployment outcomes). ACD(ii) gives their
  impossibility.

* The wall mechanism in L2 is the architectural response to ACD(ii):
  when a proactive measurement is known to be counterfactual, fall
  back on an architectural invariant (the wall condition) rather than
  on a verdict.

This file replaces the §4.2 observation with a theorem. The observation
stands on a formal foundation shared with the rest of the EvoEcos proof
tree.
-/

end EvoEcos
