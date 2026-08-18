import EvoEcos.ACD
import EvoEcos.BoundedCognition

/-
# ACD Galois Connection Structure

**Date:** 2026-05-29

## Overview

The Architecture-Counterfactual Dichotomy induces a pair of dual operators
on the lattice of world-state predicates (W → Prop, ordered pointwise):

* **V** (verifiable kernel): V(P)(w) holds iff P holds at every world
  observationally equivalent to w. V is a kernel operator:
  V(P) ≤ P, idempotent, monotone.

* **C** (counterfactual envelope): C(P)(w) holds iff P holds at some world
  observationally equivalent to w. C is a closure operator:
  P ≤ C(P), idempotent, monotone.

V and C are dual: C(P) = ¬V(¬P). The adjunction is:
  V(P) ≤ Q ↔ P ≤ C(Q)

Architectural predicates are exactly the fixed points: V(P) = P ↔ C(P) = P.

## What this file proves (0 sorry)

* `V_contractive`  — V(P) ≤ P
* `V_idempotent`   — V(V(P)) = V(P)
* `V_monotone`     — P ≤ Q → V(P) ≤ V(Q)
* `C_extensive`    — P ≤ C(P)
* `C_idempotent`   — C(C(P)) = C(P)
* `C_monotone`     — P ≤ Q → C(P) ≤ C(Q)
* `V_and_C_dual`   — C(P) ↔ ¬V(¬P)
* `galois_adjunction_open` — P arch → (P ≤ V(Q) ↔ C(P) ≤ Q)
* `architectural_iff_V_fixed_point` — Architectural ↔ V(P) = P
* `counterfactual_iff_C_witness` — Counterfactual ↔ ∃ w, C(λw', truth w' = false) w
* `V_is_architectural` — V(obs, P) factors through obs
* `V_greatest_architectural` — V(P) is the greatest architectural below P
-/

namespace EvoEcos

open ObservationalSetup

variable {W O : Type}

/-! ## Definitions -/

/-- Verifiable kernel: V(P)(w) iff P holds at ALL obs-equivalent worlds. -/
def V (obs : W → O) (P : W → Prop) (w : W) : Prop :=
  ∀ w' : W, obs w' = obs w → P w'

/-- Counterfactual envelope: C(P)(w) iff P holds at SOME obs-equivalent world. -/
def C (obs : W → O) (P : W → Prop) (w : W) : Prop :=
  ∃ w' : W, obs w' = obs w ∧ P w'

/-! ## V is a Kernel Operator -/

/-- V is contractive: V(P) ≤ P. Instantiating with w' = w. -/
theorem V_contractive (obs : W → O) (P : W → Prop) (w : W)
    (h : V obs P w) : P w :=
  h w rfl

/-- V is idempotent: V(V(P)) = V(P). -/
theorem V_idempotent (obs : W → O) (P : W → Prop) (w : W) :
    V obs (V obs P) w ↔ V obs P w := by
  constructor
  · intro hVV w' hw'
    exact V_contractive obs P w' (hVV w' hw')
  · intro hVP w'' hw'' w''' hw'''
    have hchain : obs w''' = obs w := hw'''.trans hw''
    exact hVP w''' hchain

/-- V is monotone: P ≤ Q → V(P) ≤ V(Q). -/
theorem V_monotone (obs : W → O) (P Q : W → Prop)
    (hPQ : ∀ w, P w → Q w) (w : W) (hVP : V obs P w) : V obs Q w := by
  intro w' hw'
  exact hPQ w' (hVP w' hw')

/-! ## C is a Closure Operator -/

/-- C is extensive: P ≤ C(P). Witness w itself. -/
theorem C_extensive (obs : W → O) (P : W → Prop) (w : W) (h : P w) :
    C obs P w :=
  ⟨w, rfl, h⟩

/-- C is idempotent: C(C(P)) = C(P). -/
theorem C_idempotent (obs : W → O) (P : W → Prop) (w : W) :
    C obs (C obs P) w ↔ C obs P w := by
  constructor
  · intro hCC
    obtain ⟨w', hw', w'', hw'', hP⟩ := hCC
    have hchain : obs w'' = obs w := hw''.trans hw'
    exact ⟨w'', hchain, hP⟩
  · intro hCP
    obtain ⟨w', hw', hP⟩ := hCP
    exact ⟨w', hw', w', rfl, hP⟩

/-- C is monotone: P ≤ Q → C(P) ≤ C(Q). -/
theorem C_monotone (obs : W → O) (P Q : W → Prop)
    (hPQ : ∀ w, P w → Q w) (w : W) (hCP : C obs P w) : C obs Q w := by
  obtain ⟨w', hw', hP⟩ := hCP
  exact ⟨w', hw', hPQ w' hP⟩

/-! ## The V-C Duality -/

/-- C(P) = ¬V(¬P): closure is the dual of kernel. -/
theorem V_and_C_dual (obs : W → O) (P : W → Prop) (w : W) :
    C obs P w ↔ ¬ V obs (fun w' => ¬ P w') w := by
  constructor
  · intro ⟨w', hw', hP⟩ hV
    exact hV w' hw' hP
  · intro hNotV
    by_contra hNoC
    apply hNotV
    intro w'' hw''
    change ¬P w''
    intro hP
    exact hNoC ⟨w'', hw'', hP⟩

/-! ## The Galois Adjunction -/

/-- The V-C adjunction for open (architectural) predicates:
    If P is observation-determined, then P ≤ V(Q) ↔ C(P) ≤ Q. -/
theorem galois_adjunction_open (obs : W → O) (P Q : W → Prop)
    (hPOpen : ∀ w1 w2, obs w1 = obs w2 → (P w1 ↔ P w2)) :
    (∀ w, P w → V obs Q w) ↔ (∀ w, C obs P w → Q w) := by
  constructor
  · intro hPVQ w hCP
    obtain ⟨w', hw', hP'⟩ := hCP
    exact hPVQ w' hP' w hw'.symm
  · intro hCPQ w hP w' hw'
    have hCP_w' : C obs P w' := ⟨w, hw'.symm, hP⟩
    exact hCPQ w' hCP_w'

/-! ## Architectural Predicates as Fixed Points of V -/

/-- Architectural ↔ V(P) = P. -/
theorem architectural_iff_V_fixed_point (obs : W → O) (P : W → Prop) :
    (∀ w1 w2, obs w1 = obs w2 → (P w1 ↔ P w2)) ↔
    (∀ w, V obs P w ↔ P w) := by
  constructor
  · intro hArch w
    constructor
    · intro hVP
      exact hVP w rfl
    · intro hP w' hw'
      exact (hArch w w' hw'.symm).mp hP
  · intro hVFP w1 w2 hobs
    constructor
    · intro hP
      exact (hVFP w1).mpr hP w2 hobs.symm
    · intro hP
      exact (hVFP w2).mpr hP w1 hobs

/-! ## Counterfactual Predicates and C -/

/--
Counterfactual ↔ ∃ w, C(λw', truth w' = false) w.

Requires strong surjectivity: every observation fiber contains a world
with truth = true. This is strictly stronger than surjectivity alone;
it asserts that the "true" value is represented in every fiber.

Forward: case-split on Bool values of the counterfactual witnesses.
Backward: if the C-witness world has truth = false, use strong surjectivity
to find a true world in the same fiber, producing a counterfactual pair.
-/
theorem counterfactual_iff_C_witness (S : ObservationalSetup W O)
    (hStrongSurj : ∀ o : O, ∃ w : W, S.obs w = o ∧ S.truth w = true) :
    S.Counterfactual ↔ ∃ w, C S.obs (fun w' => S.truth w' = false) w := by
  constructor
  · intro ⟨w1, w2, hobs, htruth⟩
    cases h1 : S.truth w1 <;> cases h2 : S.truth w2
    · exact False.elim (htruth (h1.trans h2.symm))
    · exact ⟨w2, w1, hobs, h1⟩
    · exact ⟨w1, w2, hobs.symm, h2⟩
    · exact False.elim (htruth (h1.trans h2.symm))
  · rintro ⟨w, w', hobs, hFalse⟩
    by_cases hw : S.truth w = true
    · refine ⟨w, w', hobs.symm, ?_⟩
      intro hEq
      rw [hEq] at hw
      rw [hFalse] at hw
      exact absurd hw Bool.false_ne_true
    · -- truth w = false. Use hStrongSurj to find a true world in the fiber.
      obtain ⟨wt, hwt_obs, hwt_true⟩ := hStrongSurj (S.obs w)
      -- hwt_obs : S.obs wt = S.obs w
      -- hwt_true : S.truth wt = true
      -- wt (true) and w' (false) with same obs via transitivity.
      -- obs wt = obs w and obs w' = obs w, so obs wt = obs w' via hwt_obs.trans hobs.symm
      -- Wait: hobs : S.obs w' = S.obs w, hwt_obs : S.obs wt = S.obs w
      -- hobs.symm : S.obs w = S.obs w'
      -- hwt_obs.trans hobs.symm : S.obs wt = S.obs w'
      -- Counterfactual needs ∃ w1 w2, obs w1 = obs w2 ∧ truth w1 ≠ truth w2
      refine ⟨wt, w', hwt_obs.trans hobs.symm, ?_⟩
      intro hEq
      rw [hEq] at hwt_true
      rw [hFalse] at hwt_true
      exact absurd hwt_true Bool.false_ne_true

/-! ## Additional Properties -/

/-- V produces an architectural (observation-determined) predicate. -/
theorem V_is_architectural (obs : W → O) (P : W → Prop)
    (w1 w2 : W) (hobs : obs w1 = obs w2) :
    V obs P w1 ↔ V obs P w2 := by
  constructor
  · intro hVP w' hw'
    have hchain : obs w' = obs w1 := hw'.trans hobs.symm
    exact hVP w' hchain
  · intro hVP w' hw'
    have hchain : obs w' = obs w2 := hw'.trans hobs
    exact hVP w' hchain

/-- V(P) is the greatest architectural predicate below P. -/
theorem V_greatest_architectural (obs : W → O) (P Q : W → Prop)
    (hQArch : ∀ w1 w2, obs w1 = obs w2 → (Q w1 ↔ Q w2))
    (hQP : ∀ w, Q w → P w) (w : W) (hQ : Q w) : V obs P w := by
  intro w' hw'
  have hQ' : Q w' := (hQArch w w' hw'.symm).mp hQ
  exact hQP w' hQ'

/-- V-C duality for an ObservationalSetup. -/
theorem V_and_C_dual_setup (S : ObservationalSetup W O) (P : W → Prop) (w : W) :
    C S.obs P w ↔ ¬ V S.obs (fun w' => ¬ P w') w :=
  V_and_C_dual S.obs P w

end EvoEcos
