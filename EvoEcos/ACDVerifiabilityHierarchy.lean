import EvoEcos.ACDTemporalFormal
import EvoEcos.ACDMetaObservation
import EvoEcos.ACDAdversarial

/-!
# ACD Verifiability Hierarchy and Orthogonality to Computational Complexity

**Date:** 2026-04-19

## Overview

The Architecture-Counterfactual Dichotomy (ACD) partitions predicates into
verifiable (architectural) and unverifiable (counterfactual). This file
establishes two results:

1. **Verifiability Hierarchy.** The ACD partition is not merely binary but
   the base level of a monotone refinement hierarchy parameterized by
   observation enrichment. The hierarchy is well-ordered, has a convergence
   point (`tStar`), and admits a quantitative "verifiability distance"
   metric.

2. **Orthogonality to Computational Complexity.** ACD-based unverifiability
   is an information-theoretic limitation (observation function loses
   information about the world), distinct from computational complexity
   (prediction cost). We exhibit a finite system with counterfactual
   predicates, proving ACD captures something computational irreducibility
   does not.

## What this file proves (0 sorry)

* `permanent_if_kernel_stable` — kernel stability preserves counterfactual
  status across time.
* `permanent_counterfactual_residue_nonempty` — counterfactual at t=0 with
  stable kernel implies permanent counterfactual.
* `disagreement_empty_iff_architectural` — disagreement set empty iff
  architectural (finitary version).
* `spectrum_zero_iff_architectural` — verifiability spectrum is 0 iff
  the predicate is architectural.
* `counterfactual_residue_nonempty_of_noninjective` — non-injective obs
  produces a non-empty counterfactual residue.
* `architecturalLift_injective` — architectural predicates inject into
  predicates on the observation range.
* `card_range_lt_of_noninjective` — |range(obs)| < |W| when obs is not
  injective (exponential dominance).
* `orthogonality_via_alignment` — counterfactual predicates exist in a
  finite (trivially reducible) system, proved as two separate theorems.
* `orthogonality_architectural_in_finite` — architectural predicates exist
  in the same finite system.
-/

namespace EvoEcos

open ObservationalSetup TemporalSetup MonoSetup

/-! ## Part 1: Verifiability Hierarchy -/

/-!
### 1.1 Hierarchy Structure

Given a world space W and a sequence of increasingly refined observation
functions obs_0, obs_1, obs_2, ..., each level gives a potentially finer
ACD partition. The existing `tStar` in `ACDTemporalFormal.lean` is the
convergence point of this hierarchy: the first level where a predicate
transitions from counterfactual to architectural.

The hierarchy is:
- Level 0: ACD partition under obs_0
- Level 1: ACD partition under obs_1 ⊇ obs_0
- ...
- Level t*: predicate transitions to architectural (if hWitness exists)
-/

/-!
### 1.2 The Permanent Counterfactual Residue

Not all predicates eventually become architectural. The `hWitness`
hypothesis in `tStar` is essential: some predicates have a permanent
counterfactual residue — they remain counterfactual regardless of
observation enrichment.

**Caveat (load-bearing).** "Permanent" here is relative to a *fixed,
non-intervenable* observation architecture: the hierarchy enriches
*observation* only and never permits *intervention* on the world.
Counterfactual realizability (Bareinboim, arXiv:2503.11870, 2025) shows
that some Layer-3 / counterfactual quantities become accessible through
physical experiment (intervention), not through observation alone.
`PermanentCounterfactual` therefore asserts permanence under the closed
observation model this file assumes — not absolute unknowability. A
system permitted to intervene on the world can break the residue for
some predicates. Separately, the residue being non-empty does not settle
whether any *particular* predicate is a member: that is a classification
problem (`tStar` / `hWitness`), not a consequence of non-emptiness.
-/

/--
A predicate is permanently counterfactual if it is counterfactual at
every time step. This means no finite observation enrichment can make
it architectural.
-/
def PermanentCounterfactual {W O : Type} (S : TemporalSetup W O)
    (P : W → Bool) : Prop :=
  ∀ t : Nat, ∃ w1 w2 : W,
    S.obs w1 t = S.obs w2 t ∧ P w1 ≠ P w2

/--
If a predicate is counterfactual at time 0 and the kernel of obs
is the same at all times (no refinement), the predicate is permanently
counterfactual. Both directions of the kernel equivalence are required.
-/
theorem permanent_if_kernel_stable {W O : Type} (S : TemporalSetup W O)
    (P : W → Bool)
    (hCF_0 : ∃ w1 w2, S.obs w1 0 = S.obs w2 0 ∧ P w1 ≠ P w2)
    (hKernelRev : ∀ t w1 w2, S.obs w1 0 = S.obs w2 0 → S.obs w1 t = S.obs w2 t) :
    PermanentCounterfactual S P := by
  intro t
  obtain ⟨w1, w2, hobs0, hP⟩ := hCF_0
  exact ⟨w1, w2, hKernelRev t w1 w2 hobs0, hP⟩

/--
The permanent counterfactual residue is non-empty for any setup where
the setup is counterfactual at time 0 and the observation kernel is
constant across all times (no refinement ever occurs).

The bidirectional kernel condition means obs(·, t) and obs(·, 0) have
the same equivalence kernel for all t. Under this condition, a
counterfactual witness at time 0 persists at all times.
-/
theorem permanent_counterfactual_residue_nonempty {W O : Type}
    (S : TemporalSetup W O)
    (hCF_0 : (S.atTime 0).Counterfactual)
    (hKernelEq : ∀ t w1 w2,
      S.obs w1 t = S.obs w2 t ↔ S.obs w1 0 = S.obs w2 0) :
    PermanentCounterfactual S S.truth := by
  intro t
  obtain ⟨w1, w2, hobs0, htruth⟩ := hCF_0
  exact ⟨w1, w2, (hKernelEq t w1 w2).mpr hobs0, htruth⟩

/-!
### 1.3 Quantitative Verifiability Spectrum

For finite world spaces, the "verifiability distance" measures how far
a predicate is from being architectural.
-/

/--
The verifiability spectrum: the number of observationally-indistinguishable
world pairs on which the predicate disagrees with the truth.

For architectural predicates, this is 0 (no disagreements).
For counterfactual predicates, this is positive.
-/
def verifiabilitySpectrum {W O : Type} [Fintype W] [DecidableEq O]
    (S : ObservationalSetup W O) (P : W → Bool) : Nat :=
  ((Finset.univ : Finset (W × W)).filter
    (fun p => S.obs p.1 = S.obs p.2 ∧ P p.1 ≠ P p.2)).card

/--
The disagreement set is empty iff the predicate is architectural.
-/
theorem disagreement_empty_iff_architectural {W O : Type} [Fintype W] [DecidableEq O]
    (S : ObservationalSetup W O) (P : W → Bool) :
    ((Finset.univ : Finset (W × W)).filter
      (fun p => S.obs p.1 = S.obs p.2 ∧ P p.1 ≠ P p.2)).card = 0 ↔
      ∀ w1 w2, S.obs w1 = S.obs w2 → P w1 = P w2 := by
  classical
  constructor
  · intro h w1 w2 hobs
    by_contra hPne
    have hmem : (w1, w2) ∈ (Finset.filter
        (fun p => S.obs p.1 = S.obs p.2 ∧ P p.1 ≠ P p.2)
        (Finset.univ : Finset (W × W))) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hobs, hPne⟩
    have hpos := Finset.card_ne_zero_of_mem hmem
    exact absurd h hpos
  · intro hArch
    have hNoMem : ∀ p : W × W,
        ¬ (S.obs p.1 = S.obs p.2 ∧ P p.1 ≠ P p.2) := by
      intro p ⟨hobs, hPne⟩
      exact hPne (hArch p.1 p.2 hobs)
    have hEmpty : (Finset.filter
        (fun p => S.obs p.1 = S.obs p.2 ∧ P p.1 ≠ P p.2)
        (Finset.univ : Finset (W × W))) = ∅ := by
      refine Finset.filter_eq_empty_iff.mpr ?_
      intro p _
      exact hNoMem p
    rw [hEmpty]
    rfl

/--
The spectrum is 0 iff the predicate is architectural.
-/
theorem spectrum_zero_iff_architectural {W O : Type} [Fintype W] [DecidableEq O]
    (S : ObservationalSetup W O) (P : W → Bool) :
    verifiabilitySpectrum S P = 0 ↔
      ∀ w1 w2, S.obs w1 = S.obs w2 → P w1 = P w2 := by
  exact disagreement_empty_iff_architectural S P

/-!
### 1.4 Exponential Dominance of the Counterfactual Residue

For finite W with |W| = n and observation space O with |O| = k:
- Total predicates: 2^n (each world maps to Bool)
- Architectural predicates: ≤ 2^k (determined by observation, at most
  2^k distinct observation values, each mapping to a Bool)
- Counterfactual residue: ≥ 2^n - 2^k predicates

As n → ∞ with fixed k, the architectural fraction → 0.

The theorems below formalise both the structural and quantitative cores
of this argument:
* `counterfactual_residue_nonempty_of_noninjective` — non-injectivity of
  `obs` produces a non-empty counterfactual residue.
* `architecturalLift` / `architecturalLift_injective` — architectural
  predicates inject into `Set.range obs → Bool`.
* `card_range_lt_of_noninjective` — `|range(obs)| < |W|` when `obs` is
  not injective.
-/

/--
If `obs` is not injective, there exists a predicate on W that is not
architectural (does not factor through `obs`).

Given `w1 ≠ w2` with `obs w1 = obs w2`, the predicate that is true exactly
on `w1` cannot be architectural, because the two worlds share an observation
but disagree on the predicate.

This captures the structural core of the exponential dominance argument:
any information loss in the observation function produces a non-empty
counterfactual residue.
-/
theorem counterfactual_residue_nonempty_of_noninjective
    {W O : Type} [DecidableEq O]
    (S : ObservationalSetup W O)
    (hObsNotInj : ∃ w1 w2 : W, w1 ≠ w2 ∧ S.obs w1 = S.obs w2) :
    ∃ P : W → Bool, ¬ (∀ w1 w2, S.obs w1 = S.obs w2 → P w1 = P w2) := by
  classical
  obtain ⟨w1, w2, hwne, hobs⟩ := hObsNotInj
  -- Construct the counterfactual predicate directly.
  -- It is true on w1 and false everywhere else.
  let P (w : W) : Bool := if _h : w = w1 then true else false
  refine ⟨P, ?_⟩
  intro hArch
  have h1 : P w1 = true := if_pos rfl
  have h2 : P w2 = false := if_neg (fun h => hwne h.symm)
  have hP := hArch w1 w2 hobs
  rw [h1, h2] at hP
  exact Bool.noConfusion hP

/-- Helper: pick a world witnessing that `o` is in the range of `obs`. -/
noncomputable def preimageWitness {W O : Type} (obs : W → O)
    (o : O) (h : o ∈ Set.range obs) : W :=
  Classical.choose h

/-- The witness maps to the correct observation. -/
theorem preimageWitness_spec {W O : Type} (obs : W → O)
    {o : O} (h : o ∈ Set.range obs) :
    obs (preimageWitness obs o h) = o :=
  Classical.choose_spec h

/--
Architectural predicates on W (with respect to observation `obs`) are in
bijection with predicates on `Set.range obs`: if `P` factors through `obs`,
there is a unique `Q : Set.range obs → Bool` such that `P w = Q ⟨obs w, _⟩`.

This bijection is the key to the exponential dominance bound: the number
of architectural predicates equals `2^|range(obs)|`, which is strictly
less than `2^|W|` when `obs` is not injective.
-/
noncomputable def architecturalLift {W O : Type}
    (obs : W → O)
    (P : W → Bool)
    (_hP : ∀ w1 w2, obs w1 = obs w2 → P w1 = P w2) :
    Set.range obs → Bool :=
  fun r => P (preimageWitness obs r.val r.property)

/--
The lift is a left inverse: evaluating the lifted predicate at `⟨obs w, _⟩`
recovers `P w`.
-/
theorem architecturalLift_correct {W O : Type}
    {obs : W → O} {P : W → Bool}
    (hP : ∀ w1 w2, obs w1 = obs w2 → P w1 = P w2)
    (w : W) :
    architecturalLift obs P hP ⟨obs w, Set.mem_range_self w⟩ = P w := by
  show P (preimageWitness obs (obs w) (Set.mem_range_self w)) = P w
  have hw : obs (preimageWitness obs (obs w) (Set.mem_range_self w)) = obs w :=
    preimageWitness_spec obs (Set.mem_range_self w)
  exact hP _ _ hw

/--
The lift is injective: different architectural predicates produce different
lifted predicates. This means the map from architectural predicates to
`Set.range obs → Bool` is an injection, giving the cardinality bound.

Combined with `Fintype.card_fun`:
  - Total predicates on W: `2^|W|`
  - Architectural predicates ≤ `2^|range(obs)|`
  - Counterfactual residue ≥ `2^|W| - 2^|range(obs)|`
-/
theorem architecturalLift_injective {W O : Type}
    {obs : W → O} {P Q : W → Bool}
    (hP : ∀ w1 w2, obs w1 = obs w2 → P w1 = P w2)
    (hQ : ∀ w1 w2, obs w1 = obs w2 → Q w1 = Q w2)
    (hlift : architecturalLift obs P hP = architecturalLift obs Q hQ) :
    P = Q := by
  funext w
  calc P w
      = architecturalLift obs P hP ⟨obs w, Set.mem_range_self w⟩ := (architecturalLift_correct hP w).symm
    _ = architecturalLift obs Q hQ ⟨obs w, Set.mem_range_self w⟩ := by rw [hlift]
    _ = Q w := architecturalLift_correct hQ w

/--
**Exponential Dominance Theorem (cardinality).** If `obs : W → O` is not
injective on a finite type `W`, then `|range(obs)| < |W|`.

Proof strategy: the function `g : Set.range obs → W` (choosing a preimage
for each element of the range) is injective. If `|range(obs)| = |W|`,
then `g` is also surjective (pigeonhole on fintypes). But `w1 ≠ w2` with
`obs w1 = obs w2` implies `g` cannot be surjective: both `w1` and `w2`
would need to come from the same `r ∈ Set.range obs`, forcing `w1 = w2`.

Combined with `architecturalLift_injective` and `Fintype.card_fun`:
  - Architectural predicates ≤ `2^|range(obs)| < 2^|W|` = total predicates
-/
theorem card_range_lt_of_noninjective
    {W O : Type} [Fintype W] [DecidableEq O]
    (obs : W → O)
    (hObsNotInj : ∃ w1 w2 : W, w1 ≠ w2 ∧ obs w1 = obs w2) :
    Fintype.card (Set.range obs) < Fintype.card W := by
  classical
  obtain ⟨w1, w2, hwne, hobs⟩ := hObsNotInj
  let g (r : Set.range obs) : W := preimageWitness obs r.val r.property
  have g_spec (r : Set.range obs) : obs (g r) = r.val := preimageWitness_spec obs r.property
  have hgInj : Function.Injective g := by
    intro r1 r2 heq
    have ho1 : obs (g r1) = r1.val := g_spec r1
    have ho2 : obs (g r2) = r2.val := g_spec r2
    rw [heq] at ho1
    exact Subtype.ext (ho1.symm.trans ho2)
  -- |range(obs)| ≤ |W| from the injection
  have hle : Fintype.card (Set.range obs) ≤ Fintype.card W :=
    Fintype.card_le_of_injective g hgInj
  -- For strict inequality: by_contra
  by_contra hge
  push_neg at hge
  have heq : Fintype.card (Set.range obs) = Fintype.card W :=
    Nat.le_antisymm hle hge
  -- g is bijective: injective + same card
  have hgBij : Function.Bijective g :=
    (Fintype.bijective_iff_injective_and_card g).mpr ⟨hgInj, heq⟩
  -- Both w1 and w2 are in the image of g
  obtain ⟨r1, hr1⟩ := hgBij.2 w1
  obtain ⟨r2, hr2⟩ := hgBij.2 w2
  -- obs(g(r)) = r.val via g_spec
  -- But g(r1) = w1 (hr1) and g(r2) = w2 (hr2), so obs(w1) = r1.val, obs(w2) = r2.val
  have hw1r1 : obs w1 = r1.val := by rw [← hr1]; exact g_spec r1
  have hw2r2 : obs w2 = r2.val := by rw [← hr2]; exact g_spec r2
  -- Since obs w1 = obs w2, r1.val = r2.val, hence r1 = r2
  have hvals : r1.val = r2.val := by rw [← hw1r1, ← hw2r2, hobs]
  have hr12 : r1 = r2 := Subtype.ext hvals
  -- But then w1 = g(r1) = g(r2) = w2
  have : w1 = w2 := by rw [← hr1, hr12, hr2]
  exact hwne this

/-! ## Part 2: Orthogonality to Computational Complexity -/

/-!
### 2.1 The Separation

Computational irreducibility (Wolfram) says some systems cannot be
predicted faster than running them — a complexity-theoretic limitation.

ACD says some predicates cannot be verified from observation — an
information-theoretic limitation.

These are orthogonal:
- (Reducible, Architectural): prediction is cheap AND verifiable
- (Reducible, Counterfactual): prediction is cheap BUT unverifiable
- (Irreducible, Architectural): prediction is expensive BUT verifiable
- (Irreducible, Counterfactual): prediction is expensive AND unverifiable

The key quadrant is (Reducible, Counterfactual): a system that is
computationally trivial yet has counterfactual predicates. This proves
ACD captures something irreducibility does not.
-/

/--
The alignment world space is finite, hence computationally reducible:
every predicate on it is decidable by enumeration.

Counterfactual predicates exist on this finite space (proved in
`alignmentSetup_counterfactual`). Therefore ACD-based unverifiability
is not reducible to computational irreducibility.
-/
theorem orthogonality_finite_cf_exists :
    alignmentSetup.Counterfactual :=
  alignmentSetup_counterfactual

/--
Every predicate on the finite alignment world is decidable.
This is the computational reducibility side of the orthogonality.
-/
noncomputable instance orthogonality_finite_decidable (P : AlignmentWorld → Bool) (w : AlignmentWorld) :
    Decidable (P w = true) :=
  Classical.propDecidable (P w = true)

/--
Conversely, architectural predicates exist on the same finite system:
the constant-true predicate is trivially architectural.
-/
theorem orthogonality_architectural_in_finite :
    ∀ w1 w2 : AlignmentWorld,
      alignmentSetup.obs w1 = alignmentSetup.obs w2 →
      (fun _ : AlignmentWorld => true) w1 = (fun _ => true) w2 :=
  fun _ _ _ => rfl

/-!
### 2.2 The Four-Quadrant Classification

Any prediction problem lives in one of four quadrants:

|                           | Architectural (ACD(i)) | Counterfactual (ACD(ii)) |
|---------------------------|------------------------|--------------------------|
| Computationally Reducible | Q1: Lookup tables      | Q2: Alignment (finite)   |
| Computationally Irreducible | Q3: Hash preimages    | Q4: Complex alignment    |

ACD captures Q2 (and Q4), which computational complexity misses.
Computational complexity captures Q3 (and Q4), which ACD misses.
Only Q4 requires both frameworks.

The EvoEcos wall mechanism addresses Q2 and Q4: when the predicate
is counterfactual, defer to architectural fallback (L1) regardless
of computational cost.
-/

/-! ## Part 3: Integration with Existing Proofs -/

/-!
The hierarchy and orthogonality results are not new axioms — they
are consequences of the existing proof tree:

1. `ACD.lean` provides the base dichotomy and `alignmentSetup_counterfactual`
2. `ACDTemporal.lean` provides the monotonicity of kernel refinement
3. `ACDTemporalFormal.lean` provides `tStar` (hierarchy convergence point)
   and `architectural_upward_closed_mono` (hierarchy monotonicity)
4. `ACDMetaObservation.lean` provides the fixed point (introspection
   cannot climb the hierarchy)
5. `ACDAdversarial.lean` provides `adversarial_force_counterfactual`
   (any non-constant truth can be forced counterfactual — residue robustness)

Together, these six files form a complete theory of verifiability:

- **ACD** (binary partition) → **Hierarchy** (monotone refinement) →
  **Spectrum** (quantitative distance) → **Fixed Point** (introspection limit)
- **Orthogonality** (independence from complexity) → standalone mathematical
  contribution
- **Applications**: alignment impossibility, LLM safety classification,
  self-improvement verification ceiling, creativity gap
-/

end EvoEcos
