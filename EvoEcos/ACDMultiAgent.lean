import EvoEcos.ACD

/-!
# ACD Extension: Multi-Agent Observations

**Date:** 2026-04-15

Multiple agents observe different aspects of the world. Their combined
observation is the product of individual observations.

## What this file proves (0 sorry)

* `combined_stronger` — architectural_i implies architectural_combined.
* `complementary_rescue` — combined architectural iff complementary.
* `agent_loss_counterfactual` — losing a critical agent makes setup CF.

-/

namespace EvoEcos

open ObservationalSetup

/-! ## Multi-Agent Setup -/

structure MultiAgentSetup (W : Type) (O_i : Type) (n : Nat) where
  obs_i : Fin n → W → O_i
  truth : W → Bool

namespace MultiAgentSetup

variable {W O_i : Type} {n : Nat} (S : MultiAgentSetup W O_i n)

/-- Combined observation: vector of all agents' observations. -/
def obsCombined (w : W) : Fin n → O_i :=
  fun i => S.obs_i i w

/-- The combined setup as a standard ObservationalSetup. -/
def combinedSetup : ObservationalSetup W (Fin n → O_i) where
  obs   := S.obsCombined
  truth := S.truth

/-- Per-agent setup: agent i in isolation. -/
def agentSetup (i : Fin n) : ObservationalSetup W O_i where
  obs   := S.obs_i i
  truth := S.truth

/-! ## Key Theorems -/

/--
If any single agent is architectural, the combined setup is also architectural.
-/
theorem combined_stronger (i : Fin n)
    (hArch : ∀ w1 w2, S.obs_i i w1 = S.obs_i i w2 → S.truth w1 = S.truth w2) :
    ∀ w1 w2, S.obsCombined w1 = S.obsCombined w2 → S.truth w1 = S.truth w2 := by
  intro w1 w2 hobs
  have hi : S.obs_i i w1 = S.obs_i i w2 := by
    have : S.obsCombined w1 i = S.obsCombined w2 i := congrFun hobs i
    exact this
  exact hArch w1 w2 hi

/--
Combined is counterfactual implies every individual is counterfactual.
-/
theorem combined_cf_implies_all_cf
    (hCF : ∃ w1 w2, S.obsCombined w1 = S.obsCombined w2 ∧ S.truth w1 ≠ S.truth w2)
    (i : Fin n) :
    ∃ w1 w2, S.obs_i i w1 = S.obs_i i w2 ∧ S.truth w1 ≠ S.truth w2 := by
  obtain ⟨w1, w2, hobs, htruth⟩ := hCF
  exact ⟨w1, w2, congrFun hobs i, htruth⟩

/--
Combined is architectural iff agents collectively distinguish all
counterfactual pairs.
-/
theorem complementary_rescue :
    (∀ w1 w2, S.obsCombined w1 = S.obsCombined w2 → S.truth w1 = S.truth w2) ↔
      ∀ w1 w2, S.truth w1 ≠ S.truth w2 →
        ∃ i : Fin n, S.obs_i i w1 ≠ S.obs_i i w2 := by
  constructor
  · intro hArch w1 w2 hne
    by_contra hall
    push_neg at hall
    have heq : S.obsCombined w1 = S.obsCombined w2 := by
      ext i
      exact hall i
    exact hne (hArch w1 w2 heq)
  · intro hComp w1 w2 hobs
    by_contra htruth
    obtain ⟨i, hi⟩ := hComp w1 w2 htruth
    exact hi (congrFun hobs i)

/-! ## Agent Loss -/

/--
Degraded setup: agent j's observation replaced by a default value.
-/
def degradedObs (j : Fin n) (default : O_i) (w : W) (i : Fin n) : O_i :=
  if i = j then default else S.obs_i i w

/--
Agent j is *critical*: it distinguishes some pair that no other agent can.
-/
def IsCritical (j : Fin n) : Prop :=
  ∃ w1 w2 : W,
    S.obs_i j w1 ≠ S.obs_i j w2 ∧
    (∀ i : Fin n, i ≠ j → S.obs_i i w1 = S.obs_i i w2)

/--
Losing a critical agent makes the degraded setup counterfactual.
-/
theorem agent_loss_counterfactual {j : Fin n} (default : O_i)
    (hCrit : S.IsCritical j)
    (hTruth : ∀ w1 w2,
      S.obs_i j w1 ≠ S.obs_i j w2 →
      (∀ i : Fin n, i ≠ j → S.obs_i i w1 = S.obs_i i w2) →
      S.truth w1 ≠ S.truth w2) :
    ∃ w1 w2, S.degradedObs j default w1 = S.degradedObs j default w2 ∧ S.truth w1 ≠ S.truth w2 := by
  obtain ⟨w1, w2, hj, hothers⟩ := hCrit
  refine ⟨w1, w2, ?_, hTruth w1 w2 hj hothers⟩
  ext i
  simp only [degradedObs]
  split
  · rfl
  · exact hothers i ‹_›

end MultiAgentSetup

end EvoEcos
