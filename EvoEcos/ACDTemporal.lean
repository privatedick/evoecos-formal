import EvoEcos.ACD

/-!
# ACD Extension: Temporal Observations

**Date:** 2026-04-15

Observations accumulate over time. A predicate that is counterfactual at time
t may become architectural at time t+k as the observation function refines.

## What this file proves (0 sorry)

* `acd_temporal` — ACD at every time slice.
* `architectural_upward_closed` — once architectural, stays architectural.
* `counterfactual_transition` — conditions for CF → Arch transition.
* `wall_release_iff_architectural` — wall releases iff architectural.

-/

namespace EvoEcos

open ObservationalSetup

/-! ## Temporal Setup -/

/--
A temporal observational setup has an observation function indexed by time.
At each time t, obs w t may be more refined than at earlier times.
-/
structure TemporalSetup (W O : Type) where
  obs   : W → Nat → O
  truth : W → Bool

namespace TemporalSetup

variable {W O : Type} (S : TemporalSetup W O)

/-- The setup at time t, as a standard ObservationalSetup. -/
def atTime (t : Nat) : ObservationalSetup W O where
  obs   := fun w => S.obs w t
  truth := S.truth

/-- Architectural status at time t. -/
def ArchitecturalAt (t : Nat) : Prop :=
  Architectural (S.atTime t)

/-- Counterfactual status at time t. -/
def CounterfactualAt (t : Nat) : Prop :=
  Counterfactual (S.atTime t)

/-! ## ACD at Every Time Slice -/

/-- ACD holds at every time slice. -/
theorem acd_temporal (t : Nat) :
    S.ArchitecturalAt t ∨ S.CounterfactualAt t :=
  ACD (S.atTime t)

/-- Partition theorem at each time slice. -/
theorem temporal_partition (t : Nat) :
    S.ArchitecturalAt t ↔ ¬ S.CounterfactualAt t :=
  architectural_iff_not_counterfactual (S.atTime t)

/-! ## Monotonic Refinement -/

/--
Observation at time t2 refines observation at time t1: the kernel of
obs(·, t2) is contained in the kernel of obs(·, t1).
-/
def Refines (t1 t2 : Nat) : Prop :=
  ∀ w1 w2 : W, S.obs w1 t2 = S.obs w2 t2 → S.obs w1 t1 = S.obs w2 t1

/-- Once architectural, stays architectural under refinement. -/
theorem architectural_upward_closed {t k : Nat}
    (hArch : S.ArchitecturalAt t)
    (hRefine : S.Refines t (t + k)) :
    S.ArchitecturalAt (t + k) := by
  intro w1 w2 hobs_later
  have hobs_earlier := hRefine w1 w2 hobs_later
  exact hArch w1 w2 hobs_earlier

/-! ## Counterfactual → Architectural Transition -/

/--
A pair of worlds is separated at time t if their observations differ.
-/
def SeparatedAt (w1 w2 : W) (t : Nat) : Prop :=
  S.obs w1 t ≠ S.obs w2 t

/--
If observation at time t+k refines observation at time t, and all pairs that
share observation at t and disagree on truth become separated by t+k, then
the setup is architectural at t+k.

The refinement hypothesis is essential: we need to pull back equality at t+k
to equality at t, which refinement provides.
-/
theorem counterfactual_transition {t k : Nat}
    (hRefine : S.Refines t (t + k))
    (hAllSep : ∀ w1 w2,
      S.obs w1 t = S.obs w2 t → S.truth w1 ≠ S.truth w2 →
      S.SeparatedAt w1 w2 (t + k)) :
    S.ArchitecturalAt (t + k) := by
  intro w1 w2 hobs_k
  by_contra htruth
  have hobs_t := hRefine w1 w2 hobs_k
  exact hAllSep w1 w2 hobs_t htruth hobs_k

/-! ## Wall Release Condition -/

/--
The temporal wall theorem: it is safe to commit at time t iff
the setup is architectural at time t.
-/
theorem wall_release_iff_architectural (t : Nat) :
    S.ArchitecturalAt t ↔ ¬ S.CounterfactualAt t :=
  temporal_partition S t

end TemporalSetup

end EvoEcos
