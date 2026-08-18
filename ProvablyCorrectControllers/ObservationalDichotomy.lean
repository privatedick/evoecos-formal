/-
Architecture-Counterfactual Dichotomy (ACD)
============================================

A structural theorem about measurement and verification. Given any
observational setup (a projection from "worlds" to "observations" plus
a truth predicate), exactly one of two classes holds:

1. **Architectural**: The truth predicate factors through the observation.
   Observationally equivalent worlds always agree on truth. A perfect
   proactive estimator exists.

2. **Counterfactual**: Some pair of observationally equivalent worlds
   disagrees on truth. No proactive estimator can be perfect.

The dichotomy is exhaustive (every setup falls into exactly one class)
and the two classes have constructive consequences (verifiable vs.
impossible).

## What it proves

1. **ACD Partition** (`architectural_iff_not_counterfactual`):
   Architectural and Counterfactual are exact negations.

2. **ACD(i)** (`architectural_verifiable`):
   Architectural + realized observations => perfect estimator exists.

3. **ACD(ii)** (`counterfactual_unverifiable`):
   Counterfactual => no perfect estimator exists.

4. **ACD** (`ACD`): The combined dichotomy theorem.

5. **Meta-Observation Fixed Point** (`meta_observation_fixed_point`):
   Augmenting the observation with an architectural truth value does not
   refine the equivalence kernel. The partition is a fixed point under
   recursive self-reflection.

6. **Non-Expansion** (`architectural_class_nonexpanding`):
   A system cannot expand its architectural class through introspection.
   Counterfactual predicates remain counterfactual regardless of how many
   meta-observational layers are added.

## Why it matters

This provides a formal foundation for understanding which safety
properties of any system can be verified proactively (architectural)
and which are fundamentally unverifiable from within the system
(counterfactual). The meta-observation fixed point shows that this
boundary cannot be shifted by introspection.

## Dependencies

Mathlib only. No EvoEcos-specific types.

## References

* Original context: EvoEcos `ACD.lean` and `ACDMetaObservation.lean`
* Philosophical grounding: Epistemic limits of self-observation
  (cf. Godel, Turing, and the general theory of formal undecidability)
-/

import Mathlib.Tactic

namespace ProvablyCorrectControllers

/-! ## Observational Setup -/

/--
An observational setup packages:
* `W` — the space of worlds (full ground truth).
* `O` — the observable interface accessible to a proactive measurer.
* `obs : W → O` — the projection from worlds to observations.
* `truth : W → Bool` — the ground truth predicate to be estimated.

Two worlds `w1 w2 : W` are *observationally equivalent* iff
`obs w1 = obs w2`. A proactive estimator can only see `obs w`, not `w`
itself, and therefore cannot distinguish observationally equivalent worlds.
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

/-! ## Partition: Architectural iff not Counterfactual -/

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

/-! ## ACD(i): Architectural implies Verifiable -/

/--
**ACD(i).** If `S` is architectural and every observation is realised
by at least one world, then a perfect proactive estimator exists.

The estimator is constructed by lifting `truth` across the equivalence
kernel of `obs`: pick any witnessing world for each observation and read
its truth value. Architecturality guarantees this is well-defined.

The `realized` hypothesis is essential: without it, the estimator has
no way to produce a verdict for observations that are not instantiated.
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

/-! ## ACD(ii): Counterfactual implies Unverifiable -/

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

/-! ## Meta-Observation Fixed Point -/

/--
Given an observational setup `S`, the enhanced observation pairs the
original observation with the truth value. If `truth` is architectural,
this produces the same equivalence kernel as the original `obs`.
-/
def EnhancedObs {W O : Type} (S : ObservationalSetup W O) : W → O × Bool :=
  fun w => (S.obs w, S.truth w)

/--
The enhanced observational setup: same worlds and truth, but the
observation is now the pair `(obs w, truth w)`.
-/
def EnhancedSetup {W O : Type} (S : ObservationalSetup W O) :
    ObservationalSetup W (O × Bool) where
  obs   := EnhancedObs S
  truth := S.truth

/--
**Meta-Observation Fixed Point.** If `truth` is architectural (constant
within each `obs`-equivalence class), then the enhanced observation
`obs'(w) = (obs(w), truth(w))` yields exactly the same equivalence kernel
as `obs`. Adding architectural truth values to the observation does not
refine the partition.

**Proof idea.** Forward: `obs' w1 = obs' w2` projects to `obs w1 = obs w2`.
Reverse: if `obs w1 = obs w2`, architecturality gives `truth w1 = truth w2`,
so the pair `(obs w1, truth w1)` equals `(obs w2, truth w2)`.
-/
theorem meta_observation_fixed_point {W O : Type} (S : ObservationalSetup W O)
    (hArch : S.Architectural) :
    ∀ w1 w2, EnhancedObs S w1 = EnhancedObs S w2 ↔ S.obs w1 = S.obs w2 := by
  intro w1 w2
  constructor
  · intro h
    have : (S.obs w1, S.truth w1) = (S.obs w2, S.truth w2) := h
    exact congrArg Prod.fst this
  · intro hobs
    have htruth : S.truth w1 = S.truth w2 := hArch w1 w2 hobs
    exact Prod.ext hobs htruth

/-! ## Preservation of Architectural Status -/

/--
If the original setup is architectural, the enhanced setup is also
architectural. The truth predicate factors through the enhanced
observation just as it factored through the original.
-/
theorem enhanced_architectural {W O : Type} (S : ObservationalSetup W O)
    (hArch : S.Architectural) :
    (EnhancedSetup S).Architectural := by
  intro w1 w2 henh
  have hobs := (meta_observation_fixed_point S hArch w1 w2).mp henh
  exact hArch w1 w2 hobs

/--
Architectural predicates under `obs` remain architectural under the
enhanced observation `obs' = (obs, truth)`.
-/
theorem meta_architectural_preserved {W O : Type} (S : ObservationalSetup W O)
    (P : W → Bool) (hArch_S : S.Architectural)
    (hP_arch : ∀ w1 w2, S.obs w1 = S.obs w2 → P w1 = P w2) :
    ∀ w1 w2, EnhancedObs S w1 = EnhancedObs S w2 → P w1 = P w2 := by
  intro w1 w2 henh
  have hobs := (meta_observation_fixed_point S hArch_S w1 w2).mp henh
  exact hP_arch w1 w2 hobs

/--
Counterfactual predicates under `obs` remain counterfactual under the
enhanced observation. The meta-observation provides no new distinguishing
power.
-/
theorem meta_counterfactual_preserved {W O : Type} (S : ObservationalSetup W O)
    (P : W → Bool) (hArch_S : S.Architectural)
    (hP_cf : ∃ w1 w2, S.obs w1 = S.obs w2 ∧ P w1 ≠ P w2) :
    ∃ w1 w2, EnhancedObs S w1 = EnhancedObs S w2 ∧ P w1 ≠ P w2 := by
  obtain ⟨w1, w2, hobs, hP⟩ := hP_cf
  exact ⟨w1, w2, (meta_observation_fixed_point S hArch_S w1 w2).mpr hobs, hP⟩

/-! ## Non-Expansion of the Architectural Class -/

/--
**Architectural Class Non-Expansion.** A system whose truth predicate is
architectural cannot expand its architectural class through self-reflection.

The enhanced setup has exactly the same architectural/counterfactual
classification as the original. The boundary between the knowable and
the unknowable is a fixed point: no amount of recursive meta-observation
can shift a predicate from the counterfactual class to the architectural
class.

The iteration argument is inductive: by `enhanced_architectural`, each step
produces another architectural setup, so `meta_observation_fixed_point`
applies at every level. The partition stabilises immediately at level 0.
-/
theorem architectural_class_nonexpanding {W O : Type} (S : ObservationalSetup W O)
    (P : W → Bool) (hArch_S : S.Architectural) :
    (∀ w1 w2, S.obs w1 = S.obs w2 → P w1 = P w2) ↔
    (∀ w1 w2, EnhancedObs S w1 = EnhancedObs S w2 → P w1 = P w2) :=
  ⟨meta_architectural_preserved S P hArch_S,
   fun hP_enh w1 w2 hobs =>
     hP_enh w1 w2 ((meta_observation_fixed_point S hArch_S w1 w2).mpr hobs)⟩

end ProvablyCorrectControllers
