/-
Clamped-Update Order-Independence
=================================

**Date:** 2026-08-10

The quantum-cognition analogue of a non-commuting pair of measurement projectors
`[P_A, P_B] ≠ 0` has an exact, mundane counterpart inside EvoEcos: a *clamped
additive update*: any quality/confidence threshold moved by `± learning_rate`
and clamped to a band such as `[0.1, 1.0]`, or a belief nudged by a bounded
delta and clamped to `[0, 1]`.

This module makes that claim a theorem:

* `interior_commute` — if each individual step keeps the value inside the clamp
  band, two clamped additive updates COMMUTE, so the final belief is
  order-independent. (Their *sum* may still saturate; both orders then land on
  the same clamped value.) This is the SOUND direction, and it holds in 100% of
  randomised trajectories tested empirically.

* `saturation_breaks_commute` — a concrete witness that once a clamp boundary is
  reached the updates need NOT commute: order-dependence is possible. This is
  the source of the empirical order-dependence, and the same saturation
  mechanism that produced the LLM measurement wall in Kang (2026,
  arXiv:2607.17219).

Together they give the honest asymmetry the Python experiment found: *no
saturation ⇒ order-independent* holds always; the biconditional does not (see
`test_common_bound_saturation_is_order_independent`).

Target: 0 sorry / 0 axiom.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic

namespace EvoEcos.ClampedUpdate

/-- Clamp `x` into the closed band `[lo, hi]`. -/
def clamp (lo hi x : ℝ) : ℝ := max lo (min hi x)

/-- A single clamped additive belief update: `x ↦ clamp (x + d)`. -/
def updateClamped (lo hi d x : ℝ) : ℝ := clamp lo hi (x + d)

/-- Clamp is the identity on values already inside the band. -/
theorem clamp_eq_self {lo hi y : ℝ} (h1 : lo ≤ y) (h2 : y ≤ hi) :
    clamp lo hi y = y := by
  unfold clamp
  rw [min_eq_right h2, max_eq_right h1]

/-- **Sound direction.** If each single step from `x` stays inside the band, the
two clamped updates commute — the final belief is independent of the order in
which the two pieces of evidence arrive.

Note the hypotheses are only about the *individual* steps `x + a` and `x + b`.
The combined value `x + a + b` may well saturate: both orders then reduce to the
same `clamp (x + a + b)`, so commutation still holds. Informally: *if each piece
of evidence alone keeps the belief in band, order does not matter — even if their
sum saturates.* -/
theorem interior_commute {lo hi x a b : ℝ}
    (hxa1 : lo ≤ x + a) (hxa2 : x + a ≤ hi)
    (hxb1 : lo ≤ x + b) (hxb2 : x + b ≤ hi) :
    updateClamped lo hi b (updateClamped lo hi a x)
      = updateClamped lo hi a (updateClamped lo hi b x) := by
  unfold updateClamped
  rw [clamp_eq_self hxa1 hxa2, clamp_eq_self hxb1 hxb2]
  congr 1
  ring

/-- **Saturation witness.** With band `[0, 1]`, start `9/10`, deltas `+1/5` and
`-1/5`: applying `+1/5` first saturates at `1` and loses the excess, so the two
orders end at `8/10` vs `9/10`. Clamped updates therefore do NOT commute in
general once a boundary is reached. -/
theorem saturation_breaks_commute :
    ∃ lo hi x a b : ℝ,
      updateClamped lo hi b (updateClamped lo hi a x)
        ≠ updateClamped lo hi a (updateClamped lo hi b x) := by
  refine ⟨0, 1, 9/10, 1/5, -1/5, ?_⟩
  norm_num [updateClamped, clamp, min_def, max_def]

end EvoEcos.ClampedUpdate
