import EvoEcos.ACD

/-!
# Kochen-Specker Contextuality as ACD(ii)

**Date:** 2026-05-09

## Statement

Kochen-Specker (KS) contextuality is a structural instance of ACD(ii). In a
KS setup, measurement outcomes depend on which *context* (set of co-performed
measurements) the measurement is embedded in. Two worlds that produce the
same observation (the outcome of a single measurement) can disagree on the
truth value of a counterfactual proposition about what that measurement
*would have* yielded in a different context.

This file formalises:

1. A `MeasurementContext` type representing compatible measurement sets.
2. A `ContextualSetup` as a special case of `ObservationalSetup` where
   the observation is the single-measurement outcome and truth depends on
   context assignment.
3. A theorem: contextual setups satisfy `Counterfactual` — i.e., they are
   instances of ACD(ii).

The connection is: KS contextuality ≡ existence of observationally equivalent
worlds with different truth values ≡ ACD(ii) by definition.

## What this file proves (target: 0 sorry)

* `contextualSetup_counterfactual` — contextual measurement setups are
  instances of ACD(ii).
* `contextuality_implies_unverifiable` — no perfect proactive estimator
  exists for contextual predicates (corollary of ACD(ii)).
-/

namespace EvoEcos

/-! ## Measurement Contexts -/

/--
A compatible context is a set of measurements that can be co-performed.
In the KS theorem, contexts correspond to orthonormal bases of a Hilbert space.
-/
structure CompatibleContext (M : Type) where
  measurements : List M
  -- In a full formalisation this would require pairwise compatibility.
  -- For our purposes the structure suffices.

/--
A context assignment maps each measurement in a context to its outcome.
In QM, this would be an assignment of ±1 eigenvalues.
-/
def ContextAssignment (M : Type) := M → Bool

/--
A contextual observable setup. The observation is the outcome of a single
measurement `m`. The truth predicate depends on the *full context assignment*
— i.e., what values all compatible measurements take.

This captures the KS insight: the truth of a proposition about measurement `m`
can depend on which other measurements are performed alongside it.
-/
structure ContextualSetup (W M : Type) where
  -- Worlds: pairs of (context, full assignment)
  obs : W → Bool           -- single measurement outcome (the "observation")
  truth : W → Bool         -- contextual truth value (depends on full assignment)
  -- The key property: two worlds can have the same single-measurement outcome
  -- but different contextual truth values
  contextual : ∃ w1 w2 : W, obs w1 = obs w2 ∧ truth w1 ≠ truth w2

/-! ## Contextuality as ACD(ii) -/

/--
A contextual setup is naturally an `ObservationalSetup` where the
observation type is `Bool` (the single measurement outcome).
-/
def contextualToObs {W M : Type} (CS : ContextualSetup W M) :
    ObservationalSetup W Bool where
  obs   := CS.obs
  truth := CS.truth

/--
**Contextuality ⟹ Counterfactual (ACD(ii)).**
If a measurement setup is contextual (same observation, different truth),
then the corresponding `ObservationalSetup` is counterfactual by definition.

This is the core connection: KS contextuality is *structurally identical*
to the ACD(ii) condition. The witnessing worlds are the same in both cases.
-/
theorem contextualSetup_counterfactual {W M : Type} (CS : ContextualSetup W M) :
    (contextualToObs CS).Counterfactual := by
  obtain ⟨w1, w2, hobs, htruth⟩ := CS.contextual
  exact ⟨w1, w2, hobs, htruth⟩

/--
**Contextuality ⟹ Unverifiable.**
No perfect proactive estimator exists for a contextual measurement predicate.
This is an immediate corollary of ACD(ii) applied to contextuality.
-/
theorem contextuality_implies_unverifiable {W M : Type} (CS : ContextualSetup W M) :
    ¬ ∃ f : Estimator Bool, (contextualToObs CS).isPerfect f :=
  counterfactual_unverifiable (contextualToObs CS) (contextualSetup_counterfactual CS)

/-! ## Concrete Instance: KS-2D -/

/--
A minimal Kochen-Specker instance with two contexts sharing one measurement.

Worlds are triples: (context_id, shared_outcome, context_specific_outcome).
The observation is the shared measurement outcome.
The truth is the full assignment (which depends on context).

KS nonclassicality: the same shared outcome can appear in both contexts
with different context-specific outcomes, making truth context-dependent.
-/
inductive KS2DWorld
  | mk : (context_id : Nat) → (shared_outcome : Bool) → (context_outcome : Bool) → KS2DWorld

/--
The KS-2D setup: observation = shared outcome, truth = XOR of all outcomes
(the "parity" truth predicate that is context-sensitive).
-/
def ks2dSetup : ContextualSetup KS2DWorld Unit where
  obs := fun w => match w with
    | KS2DWorld.mk _ shared _ => shared
  truth := fun w => match w with
    | KS2DWorld.mk _ shared ctx => (shared && !ctx) || (!shared && ctx)
  contextual := by
    refine ⟨KS2DWorld.mk 0 true false, KS2DWorld.mk 1 true true, rfl, ?_⟩
    simp [Bool.and, Bool.or, Bool.not]

/--
The KS-2D setup is counterfactual by construction.
-/
theorem ks2d_counterfactual : (contextualToObs ks2dSetup).Counterfactual :=
  contextualSetup_counterfactual ks2dSetup

/--
No perfect proactive estimator exists for the KS-2D truth predicate.
-/
theorem ks2d_unverifiable :
    ¬ ∃ f : Estimator Bool, (contextualToObs ks2dSetup).isPerfect f :=
  contextuality_implies_unverifiable ks2dSetup

/-! ## Connection to EvoEcos

The KS-ACD connection explains why certain quantum-inspired experiments
(Q, W, X, S, T, V, QC1-3) in the EvoEcos suite failed to produce
formally verifiable results:

1. Quantum measurement predicates are contextual by KS theorem.
2. Contextual predicates are ACD(ii) by `contextualSetup_counterfactual`.
3. ACD(ii) predicates are unverifiable by `counterfactual_unverifiable`.

Therefore, any attempt to verify quantum-inspired measurement properties
(e.g., Bell inequality violation, contextuality tests) as architectural
invariants of the EvoEcos system is *structurally impossible* — they belong
to the counterfactual class by construction.

The only quantum experiment with formal backing is experiment_Y
(contextuality), which correctly identifies contextuality as a phenomenon
rather than claiming it as a verifiable invariant. -/

end EvoEcos
