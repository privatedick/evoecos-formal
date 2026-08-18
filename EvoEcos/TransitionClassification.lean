/-
Regime Transition Classification
=================================

Extends the effective theory formalism with a taxonomy of regime
transitions:

  - Soft (information-preserving): bounded loss, controlled passage
  - Hard (catastrophic): total loss, no passage possible

This is the "soft wall vs hard wall" distinction from the physics
analogy analysis. Key insight: the binary wall result from
BoundedCognition.lean (graduated walls collapse to binary) corresponds
to the hard transition case — the only architecturally sound gate is
a binary choice between "passage permitted" and "passage forbidden."

Results (target: 0 sorry):
  1. soft_preserves_information    — soft → info > 0
  2. hard_loses_all                — hard → info = 0
  3. soft_permits_passage          — soft → can use target theory
  4. hard_forbids_passage          — hard → cannot use target theory
  5. classification_dichotomy      — every transition is soft or hard
  6. zero_loss_not_hard            — info > 0 implies not hard
-/

import EvoEcos.EffectiveTheory

noncomputable section

namespace EvoEcos

/-! ## Transition Classification -/

/-- Classification of regime transitions between effective theories. -/
inductive TransitionKind where
  | soft : TransitionKind
  | hard : TransitionKind
  deriving Repr, DecidableEq

/-- A regime transition between two effective theories.
    Soft transitions preserve bounded information; hard transitions
    lose everything. -/
structure RegimeTransition where
  source : EffectiveTheory
  target : EffectiveTheory
  kind : TransitionKind
  /-- Fraction of information preserved: 1 = perfect, 0 = total loss. -/
  infoPreserved : Probability
  /-- Soft transitions preserve strictly positive information. -/
  hsoft : kind = TransitionKind.soft → infoPreserved.val > 0
  /-- Hard transitions lose all information. -/
  hhard : kind = TransitionKind.hard → infoPreserved.val = 0

namespace RegimeTransition

variable (rt : RegimeTransition)

/-! ## Core Classification Theorems -/

/-- **Result 1.** Soft transitions preserve information. -/
theorem soft_preserves_information (h : rt.kind = TransitionKind.soft) :
    rt.infoPreserved.val > 0 :=
  rt.hsoft h

/-- **Result 2.** Hard transitions lose all information. -/
theorem hard_loses_all (h : rt.kind = TransitionKind.hard) :
    rt.infoPreserved.val = 0 :=
  rt.hhard h

/-- **Result 3.** Soft transitions permit controlled passage:
    information is preserved and bounded in [0, 1]. -/
theorem soft_permits_passage (h : rt.kind = TransitionKind.soft) :
    rt.infoPreserved.val > 0 ∧ rt.infoPreserved.val ≤ 1 :=
  ⟨rt.hsoft h, rt.infoPreserved.property.2⟩

/-- **Result 4.** Hard transitions forbid passage:
    all information is lost. -/
theorem hard_forbids_passage (h : rt.kind = TransitionKind.hard) :
    rt.infoPreserved.val = 0 ∧ ¬(rt.infoPreserved.val > 0) := by
  have hz := rt.hhard h
  exact ⟨hz, by linarith⟩

/-! ## Classification Properties -/

/-- Every transition is either soft or hard. -/
theorem classification_dichotomy :
    rt.kind = TransitionKind.soft ∨ rt.kind = TransitionKind.hard := by
  cases rt.kind with
  | soft => left; rfl
  | hard => right; rfl

/-- A transition cannot be both soft and hard. -/
theorem not_both_soft_hard :
    ¬(rt.kind = TransitionKind.soft ∧ rt.kind = TransitionKind.hard) := by
  intro ⟨h1, h2⟩
  simp [h1] at h2

/-- Information preserved is always in [0, 1]. -/
theorem info_bounded :
    0 ≤ rt.infoPreserved.val ∧ rt.infoPreserved.val ≤ 1 :=
  rt.infoPreserved.property

/-- If information is preserved, the transition is not hard. -/
theorem zero_loss_not_hard (h_loss : rt.infoPreserved.val > 0) :
    rt.kind ≠ TransitionKind.hard := by
  intro h_hard
  have hz := rt.hhard h_hard
  linarith

/-! ## Connection to Binary Wall -/

/-- Hard transition at the cutoff: complete information loss AND
    the source theory is outside its validity domain.
    This connects to the binary wall from BoundedCognition.lean:
    the graduated wall (3-tier, RETIRED d=-0.597) tried to create
    soft transitions, but binary collapse shows only hard walls are
    architecturally sound. -/
theorem hard_transition_at_cutoff (E : ℝ)
    (h_hard : rt.kind = TransitionKind.hard)
    (h_above : EffectiveTheory.WallActive rt.source E) :
    rt.infoPreserved.val = 0 ∧
    ¬EffectiveTheory.InDomain rt.source E :=
  ⟨rt.hhard h_hard,
   EffectiveTheory.wall_active_not_in_domain rt.source E h_above⟩

/-- Soft transition within domain: information preserved AND
    the source theory is within its validity domain. -/
theorem soft_transition_in_domain (E : ℝ)
    (h_soft : rt.kind = TransitionKind.soft)
    (h_in : EffectiveTheory.InDomain rt.source E) :
    rt.infoPreserved.val > 0 ∧
    ¬EffectiveTheory.WallActive rt.source E :=
  ⟨rt.hsoft h_soft,
   EffectiveTheory.in_domain_not_wall rt.source E h_in⟩

end RegimeTransition

end EvoEcos

end
