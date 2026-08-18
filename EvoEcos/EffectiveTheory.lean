/-
Effective Theory Validity Domain
=================================

Formalizes effective field theory (EFT) validity domains using the
same proof architecture as EvoEcos wall mechanisms.

Structural analogy:
  EFT validity [Λ_lo, Λ_hi] ↔ L1 stability range
  Cutoff Λ_hi                ↔ Wall threshold (0.4)
  Prediction reliability     ↔ L3 planning capability
  Theory breakdown           ↔ Wall activation + L3 blocking

The proof architecture transfers because both are instances of the
"safety property at regime boundary" problem class.

Results (target: 0 sorry):
  1. wall_active_not_in_domain     — wall and domain are exclusive
  2. in_domain_not_wall            — in domain implies no wall
  3. cutoff_catastrophic           — above cutoff: wall active + unreliable
  4. domain_nonempty               — domain is inhabited (midpoint)
  5. above_cutoff_exists           — wall can activate (witness)
  6. mutual_exclusion              — three states are pairwise exclusive
-/

import EvoEcos.Invariants

noncomputable section

namespace EvoEcos

/-! ## Effective Theory -/

/-- An effective theory with bounded validity domain.
    Valid on [lowerBound, upperBound]; breaks down outside. -/
structure EffectiveTheory where
  lowerBound : ℝ
  upperBound : ℝ
  hbounds : 0 ≤ lowerBound ∧ lowerBound ≤ upperBound

namespace EffectiveTheory

variable (et : EffectiveTheory)

/-! ## Domain Predicates -/

/-- Energy E is within the validity domain. -/
def InDomain (E : ℝ) : Prop :=
  et.lowerBound ≤ E ∧ E ≤ et.upperBound

/-- Theory wall active: energy exceeds the cutoff. -/
def WallActive (E : ℝ) : Prop :=
  E > et.upperBound

/-- Energy below the lower bound of validity. -/
def BelowDomain (E : ℝ) : Prop :=
  E < et.lowerBound

/-! ## Core Theorems -/

/-- Wall active implies not in domain.
    Analog: l3_blocked_when_wall (Invariants.lean). -/
theorem wall_active_not_in_domain (E : ℝ) (h : et.WallActive E) :
    ¬et.InDomain E := by
  intro h_in
  unfold WallActive at h
  unfold InDomain at h_in
  linarith

/-- In domain implies wall not active.
    Analog: wall_deactivates_when_stable (Invariants.lean). -/
theorem in_domain_not_wall (E : ℝ) (h : et.InDomain E) :
    ¬et.WallActive E := by
  intro h_wall
  unfold InDomain at h
  unfold WallActive at h_wall
  linarith

/-- Below domain implies not in domain. -/
theorem below_not_in_domain (E : ℝ) (h : et.BelowDomain E) :
    ¬et.InDomain E := by
  intro h_in
  unfold BelowDomain at h
  unfold InDomain at h_in
  linarith

/-- In domain implies not below. -/
theorem in_domain_not_below (E : ℝ) (h : et.InDomain E) :
    ¬et.BelowDomain E := by
  intro h_below
  unfold InDomain at h
  unfold BelowDomain at h_below
  linarith

/-- Below domain implies not wall active (lowerBound ≤ upperBound). -/
theorem below_not_wall (E : ℝ) (h : et.BelowDomain E) :
    ¬et.WallActive E := by
  intro h_wall
  unfold BelowDomain at h
  unfold WallActive at h_wall
  linarith [et.hbounds.2]

/-- Wall active implies not below. -/
theorem wall_not_below (E : ℝ) (h : et.WallActive E) :
    ¬et.BelowDomain E := by
  intro h_below
  unfold WallActive at h
  unfold BelowDomain at h_below
  linarith [et.hbounds.2]

/-- Crossing the cutoff: wall active AND not in domain. -/
theorem cutoff_catastrophic (E : ℝ) (h : et.WallActive E) :
    et.WallActive E ∧ ¬et.InDomain E :=
  ⟨h, wall_active_not_in_domain et E h⟩

/-- The three states (in domain / wall active / below) are pairwise exclusive. -/
theorem mutual_exclusion (E : ℝ) :
    (et.InDomain E → ¬et.WallActive E) ∧
    (et.InDomain E → ¬et.BelowDomain E) ∧
    (et.WallActive E → ¬et.InDomain E) ∧
    (et.WallActive E → ¬et.BelowDomain E) ∧
    (et.BelowDomain E → ¬et.InDomain E) ∧
    (et.BelowDomain E → ¬et.WallActive E) :=
  ⟨in_domain_not_wall et E, in_domain_not_below et E,
   wall_active_not_in_domain et E, wall_not_below et E,
   below_not_in_domain et E, below_not_wall et E⟩

/-! ## Existence Witnesses -/

/-- Domain is nonempty: midpoint is in the domain. -/
theorem domain_nonempty :
    ∃ E : ℝ, et.InDomain E := by
  use (et.lowerBound + et.upperBound) / 2
  constructor <;> linarith [et.hbounds.1, et.hbounds.2]

/-- Energy above cutoff exists (wall can activate). -/
theorem above_cutoff_exists :
    ∃ E : ℝ, et.WallActive E := by
  use et.upperBound + 1
  unfold WallActive; linarith

/-- Energy below lower bound exists. -/
theorem below_lower_exists :
    ∃ E : ℝ, et.BelowDomain E := by
  use et.lowerBound - 1
  unfold BelowDomain; linarith

end EffectiveTheory

end EvoEcos

end
