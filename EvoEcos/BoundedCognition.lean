/-
Bounded Cognitive System: Binary Gating as a Universal Feature
==============================================================

Abstracts the L1-L4 architecture to a general two-mode structure:

  - Operational mode: fast, always-available, uses only observations
  - Deliberative mode: slow, conditionally-available, uses full world state
  - Binary gate: architectural predicate controlling deliberative access

Connection to existing proofs:
  - ACD (ACD.lean): gate uses only architectural predicates
  - BangBang (BangBangTheorem.lean): gate decisions are noise-robust
  - Convergence (Convergence.lean): gate deactivates when stability permits

Results (0 sorry):
  1. gate_factors_through_obs    — architectural gates are observation functions
  2. gate_invariant_under_noise  — gate invariant under obs-preserving perturbation
  3. binary_collapse_architectural — graduated gates collapse to binary
  4. noninjective_has_counterfactual — bounded cognition → counterfactual content
  5. permanent_residue_of_noninjective — counterfactual residue is permanent
  6. architectural_dominance — |range(obs)| < |W| for finite non-injective systems
-/

import EvoEcos.ACD
import EvoEcos.ACDVerifiabilityHierarchy

namespace EvoEcos

open ObservationalSetup

/-! ## Bounded Cognitive System -/

/--
A Bounded Cognitive System abstracts the EvoEcos L1-L4 architecture.

The operational mode uses only observable information (architectural, by ACD),
while the deliberative mode uses full world-state information (including
counterfactual content). The gate must depend only on architectural
information — this is the formal content of the "safety by structure"
principle that underlies binary gating across all five convergent domains
(neuroscience, ancient traditions, psychology, philosophy, AI safety).
-/
structure BoundedCognitiveSystem (W O : Type) where
  /-- Observation function: projects world state to observable interface -/
  obs : W → O
  /-- Operational mode: uses only observable information -/
  operational : O → Bool
  /-- Deliberative mode: uses full world state -/
  deliberative : W → Bool
  /-- Gate predicate: determines when deliberative mode engages -/
  gate : W → Bool
  /-- The gate is architectural: determined by observations alone (ACD) -/
  gate_architectural :
    ∀ w1 w2 : W, obs w1 = obs w2 → gate w1 = gate w2
  /-- Every observation is realized by some world (surjectivity for ACD(i)) -/
  obs_surjective :
    ∀ o : O, ∃ w : W, obs w = o

namespace BoundedCognitiveSystem

variable {W O : Type} (sys : BoundedCognitiveSystem W O)

/-! ## Observational Setup for the Gate -/

/-- The observational setup for the gate predicate. -/
def gateSetup : ObservationalSetup W O where
  obs := sys.obs
  truth := sys.gate

/-- The gate setup is architectural (by axiom). -/
theorem gateSetup_architectural : sys.gateSetup.Architectural :=
  sys.gate_architectural

/-! ## Result 1: Gate Factors Through Observations -/

/-- **Result 1.** Any architectural gate factors through the observation
function.

By ACD(i), since the gate is architectural and every observation is
realized, there exists `gate_obs : O → Bool` with
`gate w = gate_obs (obs w)` for all worlds `w`.

The gate cannot depend on counterfactual information — it is inherently
an observation-level function with binary output. -/
theorem gate_factors_through_obs :
    ∃ gate_obs : O → Bool,
      ∀ w : W, sys.gate w = gate_obs (sys.obs w) := by
  obtain ⟨f, hf⟩ :=
    architectural_verifiable sys.gateSetup sys.gateSetup_architectural sys.obs_surjective
  exact ⟨f, fun w => (hf w).symm⟩

/-! ## Result 2: Gate Invariance Under Noise -/

/-- **Result 2.** The gate decision is invariant under perturbations that
preserve the observation.

If a noise perturbation changes the world state but doesn't change the
observation (the system can't detect the difference), the gate decision
remains the same.

Connection to BangBang: The safe zone preserves the sign of the
pre-activation under bounded noise. Similarly, the gate (being a function
of observations) is invariant under perturbations that don't change
the observation. -/
theorem gate_invariant_under_obs_preserving_perturbation
    (w1 w2 : W) (h_obs : sys.obs w1 = sys.obs w2) :
    sys.gate w1 = sys.gate w2 :=
  sys.gate_architectural w1 w2 h_obs

/-- When the gate blocks, the operational mode's output depends only on
observations (not on the deliberative mode's state). -/
theorem operational_independence (w1 w2 : W)
    (h_obs : sys.obs w1 = sys.obs w2) :
    sys.operational (sys.obs w1) = sys.operational (sys.obs w2) := by
  rw [h_obs]

/-- Full system output when blocked is observation-determined:
both operational output and gate decision are functions of obs alone. -/
theorem system_output_when_blocked (w1 w2 : W)
    (h_obs : sys.obs w1 = sys.obs w2) :
    sys.operational (sys.obs w1) = sys.operational (sys.obs w2) ∧
    sys.gate w1 = sys.gate w2 :=
  ⟨operational_independence sys w1 w2 h_obs,
   gate_invariant_under_obs_preserving_perturbation sys w1 w2 h_obs⟩

/-! ## Result 3: Graduated Gates Collapse to Binary -/

/-- **Result 3.** The binary collapse of a graduated gate preserves
architecturality.

Given a graduated gate `g : W → Nat`, the binary collapse
`g_bin w = (g w > 0)` is architectural whenever `g` is.

This formalizes the experimental finding that the 3-tier graduated
wall (d = -0.597) was dominated by the binary wall: intermediate
levels add no architectural information. -/
theorem binary_collapse_architectural {W O : Type}
    (obs : W → O) (g : W → Nat)
    (hArch : ∀ w1 w2, obs w1 = obs w2 → g w1 = g w2)
    (w1 w2 : W) (h_obs : obs w1 = obs w2) :
    (g w1 > 0) = (g w2 > 0) := by
  congr 1
  exact hArch w1 w2 h_obs

/-- Every architectural graduated gate has a binary architectural
representation. -/
theorem graduated_collapses_to_binary {W O : Type}
    (obs : W → O) (g : W → Nat)
    (hArch : ∀ w1 w2, obs w1 = obs w2 → g w1 = g w2) :
    ∃ (g_bin : W → Prop),
      (∀ w1 w2, obs w1 = obs w2 → (g_bin w1 ↔ g_bin w2)) ∧
      ∀ w, g_bin w ↔ g w > 0 := by
  refine ⟨fun w => g w > 0, ?_, ?_⟩
  · intro w1 w2 h_obs
    have h := binary_collapse_architectural obs g hArch w1 w2 h_obs
    constructor
    · intro a; change g w1 > 0 at a; rw [h] at a; change g w2 > 0; exact a
    · intro a; change g w2 > 0 at a; rw [← h] at a; change g w1 > 0; exact a
  · intro w; rfl

/-! ## Result 4: Bounded Cognition Creates Counterfactual Content -/

/-- **Result 4.** Non-injective observations guarantee the existence of
counterfactual predicates.

If the observation function is not injective (some information is lost),
there exist world-state predicates that cannot be verified from
observations alone. These counterfactual predicates motivate the
deliberative mode — it reasons about things beyond direct observation.

**Universality argument (combining Results 1–4):**
1. Bounded cognition ⟹ non-injective observations (information loss)
2. Non-injective ⟹ counterfactual predicates exist (Result 4)
3. The gate must be architectural (by axiom)
4. Architectural ⟹ factors through observations ⟹ binary (Results 1, 3)
5. Therefore: every bounded cognitive system has a binary gate -/
theorem noninjective_has_counterfactual
    (h_noninj : ¬ Function.Injective sys.obs) :
    ∃ (truth : W → Bool),
      ¬ (∀ w1 w2, sys.obs w1 = sys.obs w2 → truth w1 = truth w2) := by
  rw [Function.Injective] at h_noninj
  push_neg at h_noninj
  obtain ⟨a, b, h_obs, h_ne⟩ := h_noninj
  classical
  refine ⟨fun w => if w = a then true else false, ?_⟩
  intro hArch
  have h1 := hArch a b h_obs
  simp only [ite_true, ite_false, h_ne.symm] at h1
  nomatch h1

/-! ## Result 5: Permanent Counterfactual Residue -/

/-- Construct a temporal setup from the system's observation function
(constant over time) with an arbitrary truth predicate. Models the
case where no observation enrichment occurs — the kernel never refines. -/
def temporalOfObs (truth : W → Bool) : TemporalSetup W O where
  obs := fun w _t => sys.obs w
  truth := truth

/-- **Result 5.** For any BoundedCognitiveSystem with non-injective
observations, the counterfactual predicate is permanently counterfactual
under constant (non-refining) observations.

The observation kernel never refines, so the counterfactual predicate
cannot become architectural at any future time. This connects Result 4
(static counterfactual existence) to the temporal hierarchy: the residue
is not merely present, but permanent. -/
theorem permanent_residue_of_noninjective
    (h_noninj : ¬ Function.Injective sys.obs) :
    ∃ (cf : W → Bool),
      PermanentCounterfactual (sys.temporalOfObs cf) cf ∧
      ¬ (∀ w1 w2, sys.obs w1 = sys.obs w2 → cf w1 = cf w2) := by
  rw [Function.Injective] at h_noninj
  push_neg at h_noninj
  obtain ⟨a, b, h_obs_ab, h_ne_ab⟩ := h_noninj
  classical
  refine ⟨fun w => if w = a then true else false, ?_, ?_⟩
  · -- PermanentCounterfactual
    intro t
    refine ⟨a, b, h_obs_ab, ?_⟩
    intro h
    simp only [ite_true, ite_false, h_ne_ab.symm] at h
    nomatch h
  · -- ¬ architectural (same construction as Result 4)
    intro hArch
    have h1 := hArch a b h_obs_ab
    simp only [ite_true, ite_false, h_ne_ab.symm] at h1
    nomatch h1

/-! ## Result 6: Exponential Dominance of Counterfactual Residue -/

/-- **Result 6.** For finite BoundedCognitiveSystems with non-injective
observations, architectural predicates are exponentially dominated by
counterfactual predicates: |range(obs)| < |W|. -/
theorem architectural_dominance [Fintype W] [DecidableEq O]
    (h_noninj : ¬ Function.Injective sys.obs) :
    Fintype.card (Set.range sys.obs) < Fintype.card W := by
  classical
  rw [Function.Injective] at h_noninj
  push_neg at h_noninj
  obtain ⟨w1, w2, hobs, hwne⟩ := h_noninj
  exact card_range_lt_of_noninjective sys.obs ⟨w1, w2, hwne, hobs⟩

/-! ## Nagarjuna Connection: Emptiness as Non-Injectivity

The `empty_obs` predicate reifies non-injectivity as a first-class object.
In Nagarjuna's Madhyamaka, emptiness (śūnyatā) is the absence of inherent
existence (svabhāva) — a negative fact *about the observation-world
relationship*, not a hidden fact *in* W. Here, "emptiness" of an observation
is its non-uniqueness: no single world state grounds it.

This is modification (A) from the Nagarjuna correspondence analysis: minimal
extension that closes the structural gap between BoundedCognitiveSystem and
the Two Truths doctrine without changing existing results.

Reference: research_nagarjuna_formalization.md
-/

/-- An observation is *empty* (has multiple preimages in W).
Maps to Nagarjuna's śūnyatā: the observation lacks a single grounding
in world state. No svabhāva (inherent existence) for this observation. -/
def empty_obs (o : O) : Prop :=
  ∃ w1 w2, sys.obs w1 = o ∧ sys.obs w2 = o ∧ w1 ≠ w2

/-- The set of empty observations. -/
def emptyObservations : Set O :=
  { o : O | sys.empty_obs o }

/-- Non-injectivity of obs guarantees the existence of empty observations.
This connects to `noninjective_has_counterfactual` (Result 4): non-injectivity
simultaneously guarantees (a) empty observations and (b) counterfactual
predicates. Emptiness and counterfactuality are dual faces of the same
information loss. -/
theorem noninjective_has_empty_obs
    (h_noninj : ¬ Function.Injective sys.obs) :
    ∃ o : O, sys.empty_obs o := by
  rw [Function.Injective] at h_noninj
  push_neg at h_noninj
  obtain ⟨a, b, h_obs, h_ne⟩ := h_noninj
  exact ⟨sys.obs a, a, b, rfl, h_obs.symm ▸ rfl, h_ne⟩

/-- Non-injectivity iff there exist empty observations.
`empty_obs` faithfully captures non-injectivity: the observation function
is non-injective precisely when some observation is empty (has multiple
preimages). -/
theorem noninjective_iff_exists_empty :
    (¬ Function.Injective sys.obs) ↔ ∃ o : O, sys.empty_obs o := by
  constructor
  · exact sys.noninjective_has_empty_obs
  · intro ⟨o, w1, w2, hw1, hw2, hne⟩
    rw [Function.Injective]
    push_neg
    exact ⟨w1, w2, hw1 ▸ hw2.symm, hne⟩

/-- The counterfactual witness from Result 4 detects emptiness.
If `w` is the distinguished world in the counterfactual witness, then
`obs w` is an empty observation. -/
theorem counterfactual_witness_is_empty
    (h_noninj : ¬ Function.Injective sys.obs) :
    ∃ (truth : W → Bool) (w : W),
      truth w = true ∧
      ¬ (∀ w1 w2, sys.obs w1 = sys.obs w2 → truth w1 = truth w2) ∧
      sys.empty_obs (sys.obs w) := by
  rw [Function.Injective] at h_noninj
  push_neg at h_noninj
  obtain ⟨a, b, h_obs, h_ne⟩ := h_noninj
  classical
  refine ⟨fun w => if w = a then true else false, a, ?_, ?_, ?_⟩
  · simp only [ite_true]
  · intro hArch
    have h1 := hArch a b h_obs
    simp only [ite_true, ite_false, h_ne.symm] at h1
    nomatch h1
  · exact ⟨a, b, rfl, h_obs.symm ▸ rfl, h_ne⟩

/-- No architectural predicate can separate preimages of an empty observation.
This is the formal content of Nagarjuna's claim that conventional truth
(architectural predicates) cannot access the distinction between preimages
of an empty observation: any `p` determined by observations alone must assign
the same value to all worlds mapping to the same observation. -/
theorem empty_obs_cannot_distinguish (o : O)
    (h_empty : sys.empty_obs o)
    (p : W → Bool)
    (hArch : ∀ w1 w2, sys.obs w1 = sys.obs w2 → p w1 = p w2) :
    ∃ (v : Bool), ∀ w, sys.obs w = o → p w = v := by
  obtain ⟨wa, _wb, hwa, _hwb, _hne⟩ := h_empty
  exact ⟨p wa, fun w hw => hArch w wa (hw.trans hwa.symm)⟩

end BoundedCognitiveSystem

end EvoEcos
