/-
Isomorphism Corollaries
=======================

Follow-on theorems from SubstrateIsomorphism.lean, exploiting the BoundedProtectivePattern
abstraction to state substrate-independent properties.

Three corollaries:

1. BoundedProtectivePattern Non-Degeneracy: every BPCS has a positive barrier gap and
   non-degenerate hysteresis band. This is a universal statement about the pattern, not
   about any specific substrate (EvoEcos or SymbolicField).

2. Property Transfer: any property P that holds for arbitrary BoundedProtectivePattern
   instances also holds for both evoecosPattern and sfPattern. This formalizes the
   substrate-independence claim of the isomorphism.

3. Wall Structural Precondition: the barrier gap being strictly positive is a necessary
   condition for the wall to be non-trivially beneficial — it ensures the system can
   reside in [survival_lb, barrier_close) (the "wall beneficial zone") for a positive
   measure of stability values. This is the structural analogue of the two-condition
   theory's "L1 evolvable" condition.

All theorems: 0 sorry, 0 new axioms beyond SubstrateIsomorphism.lean.
-/

import EvoEcos.SubstrateIsomorphism

noncomputable section

namespace EvoEcos

open BoundedProtectivePattern

/-! ## 1. Universal Non-Degeneracy -/

/-- Every BoundedProtectivePattern has a positive barrier gap and positive hysteresis band.
These are universal: they hold for any substrate (EvoEcos, SymbolicField, or other). -/
theorem bpcs_nondegeneracy (p : BoundedProtectivePattern) :
    0 < p.barrierGap ∧ 0 < p.hysteresisBand ∧ p.survival_lb < p.barrier_open :=
  ⟨p.barrierGap_pos, p.hysteresisBand_pos,
   by linarith [p.h_surv_lt_barrier, p.h_hysteresis]⟩

/-- Corollary: any two BPCS instances share non-degeneracy.
Substrate-independence of the structural guarantee. -/
theorem bpcs_shared_nondegeneracy (p1 p2 : BoundedProtectivePattern) :
    0 < p1.barrierGap ∧ 0 < p2.barrierGap ∧
    0 < p1.hysteresisBand ∧ 0 < p2.hysteresisBand :=
  ⟨p1.barrierGap_pos, p2.barrierGap_pos, p1.hysteresisBand_pos, p2.hysteresisBand_pos⟩

/-- Specifically: both EvoEcos (barrier gap = 0.4) and an arbitrary SymbolicField instance
have positive barrier gaps. Used to transfer two-condition theory structural conditions. -/
theorem evoecos_and_sf_nondegeneracy (sf : SFState) :
    0 < evoecosPattern.barrierGap ∧ 0 < (sfPattern sf).barrierGap :=
  ⟨evoecosPattern.barrierGap_pos, (sfPattern sf).barrierGap_pos⟩

/-! ## 2. Property Transfer Principle -/

/-- If a property P holds for any BoundedProtectivePattern, it holds for evoecosPattern.
Instantiation lemma — allows lifting universal BPCS properties to EvoEcos. -/
theorem bpcs_evoecos_instantiation
    (P : BoundedProtectivePattern → Prop) (h : ∀ p, P p) :
    P evoecosPattern := h evoecosPattern

/-- If a property P holds for any BoundedProtectivePattern, it holds for sfPattern sf.
Instantiation lemma — allows lifting universal BPCS properties to SymbolicField. -/
theorem bpcs_sf_instantiation (sf : SFState)
    (P : BoundedProtectivePattern → Prop) (h : ∀ p, P p) :
    P (sfPattern sf) := h (sfPattern sf)

/-- Property transfer: any universal BPCS property holds for both EvoEcos and SymbolicField.
This formalizes substrate-independence: prove once for BoundedProtectivePattern,
get both instances for free. -/
theorem bpcs_property_transfer (sf : SFState)
    (P : BoundedProtectivePattern → Prop) (h : ∀ p, P p) :
    P evoecosPattern ∧ P (sfPattern sf) :=
  ⟨h evoecosPattern, h (sfPattern sf)⟩

/-! ## 3. Wall Structural Precondition -/

/-- The "wall beneficial zone" [survival_lb, barrier_close) has positive width for any BPCS.
This is the structural analogue of the two-condition theory's L1-evolvability condition:
the system can inhabit a stability region where the wall provides benefit.

Formally: barrierGap > 0 implies there exist values in (survival_lb, barrier_close),
so the wall activation threshold is not vacuously satisfied. -/
theorem bpcs_wall_beneficial_zone_nonempty (p : BoundedProtectivePattern) :
    ∃ x : ℝ, p.survival_lb < x ∧ x < p.barrier_close := by
  exact ⟨(p.survival_lb + p.barrier_close) / 2,
         by linarith [p.h_surv_lt_barrier],
         by linarith [p.h_surv_lt_barrier]⟩

/-- The open zone (barrier_close, barrier_open) has positive width — the hysteresis band
is non-trivial. Once the wall activates, the system cannot immediately deactivate it
without moving to a strictly higher stability. -/
theorem bpcs_hysteresis_zone_nonempty (p : BoundedProtectivePattern) :
    ∃ x : ℝ, p.barrier_close < x ∧ x < p.barrier_open := by
  exact ⟨(p.barrier_close + p.barrier_open) / 2,
         by linarith [p.h_hysteresis],
         by linarith [p.h_hysteresis]⟩

/-- Combined structural precondition: both zones are non-empty, and they are disjoint.
This ensures the wall mechanism is well-defined and non-trivial for any BPCS instance. -/
theorem bpcs_wall_structure_well_defined (p : BoundedProtectivePattern) :
    (∃ x : ℝ, p.survival_lb < x ∧ x < p.barrier_close) ∧
    (∃ y : ℝ, p.barrier_close < y ∧ y < p.barrier_open) ∧
    (∀ x y : ℝ, p.survival_lb < x ∧ x < p.barrier_close →
               p.barrier_close < y → x < y) := by
  refine ⟨?_, ?_, ?_⟩
  · exact bpcs_wall_beneficial_zone_nonempty p
  · exact bpcs_hysteresis_zone_nonempty p
  · intro x y ⟨_, hx_lt⟩ hy_gt
    linarith

/-- Transfer: both EvoEcos and SymbolicField have well-defined wall structures.
The two-condition theory's structural precondition (a beneficial zone exists)
is substrate-independent — it follows from being a BoundedProtectivePattern. -/
theorem wall_structure_substrate_independent (sf : SFState) :
    (∃ x : ℝ, evoecosPattern.survival_lb < x ∧ x < evoecosPattern.barrier_close) ∧
    (∃ x : ℝ, (sfPattern sf).survival_lb < x ∧ x < (sfPattern sf).barrier_close) :=
  ⟨bpcs_wall_beneficial_zone_nonempty evoecosPattern,
   bpcs_wall_beneficial_zone_nonempty (sfPattern sf)⟩

end EvoEcos

end
