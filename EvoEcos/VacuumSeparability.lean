/-
Vacuum Separability
===================

Structural formalization of the empirically-bracketed scope condition for the
vacuum blind spot (the *why*, complementing the measured-threshold
`VacuumPerturbation` namespace in WallDomainTriple.lean).

Empirical bracket (real gymnasium CartPole-v1, 2026-05-31, SAME physics, only the
goal channel changed):
  - experiment_vacuum_cartpole.py        — COUPLED goal (move the cart to a target,
      sharing the balancing actuator): vacuum l3_goal 0.006 vs clean 0.006 → no harm;
      vacuum even improves survival. NOT a silent blind spot.
  - experiment_vacuum_cartpole_report.py — SEPARABLE goal (report a latent target on
      an independent channel): vacuum l3_goal 0.467 vs clean 0.958 → harm; wall stays
      blind (vacuum wall_fire 0.109 = clean 0.109). A silent blind spot WITH harm.

The structural claim those two poles bracket: the wall is a function of the SURVIVAL
signal only; a vacuum (zeroing the goal/context channel) is invisible to the wall at
EVERY threshold IFF zeroing it leaves the survival signal unchanged — i.e. iff the
goal channel is SEPARABLE from survival. Coupling (survival depends on the goal
channel) is exactly the condition under which some threshold can DETECT the vacuum.

Runtime coupling (src/experiments/experiment_vacuum_cartpole_report.py):
  - `Separable`  ↔ the report-task survival signal (balance only) ignores the target
      feature → wall blind (vacuum 0.109 = clean 0.109).
  - `Coupled`    ↔ the cart-target survival signal depends on the goal pursuit →
      vacuum perturbs survival → detectable / no clean blind spot.
  - `silent_blindspot_with_harm` ↔ separable + achievable goal ⇒ blind wall + degraded goal.
-/

import EvoEcos.Invariants

namespace EvoEcos
namespace VacuumSeparability

variable {α : Type*} (wi gs : α → ℝ) (vac : α → α)

/-- The goal channel is **separable** from survival: zeroing the goal/context
    channel (the `vac` operation) leaves the wall's survival signal `wi` unchanged. -/
def Separable : Prop := ∀ c, wi (vac c) = wi c

/-- The goal channel is **coupled** to survival: some configuration's survival
    signal is changed by vacuuming the goal channel. -/
def Coupled : Prop := ∃ c, wi (vac c) ≠ wi c

/-- The wall fires when the survival signal drops below a threshold; the wall is
    **blind** to the vacuum if, at every threshold, it cannot distinguish a vacuumed
    configuration from its clean counterpart. (`wi c < thr` reads "wall fires".) -/
def WallBlind : Prop := ∀ thr c, (wi (vac c) < thr ↔ wi c < thr)

/-- The goal is **achievable**: vacuuming the goal channel strictly degrades the
    goal score for some configuration (the goal genuinely depends on the channel). -/
def Achievable : Prop := ∃ c, gs (vac c) < gs c

/-- Helper: over a linear order, two reals agreeing on every strict upper-threshold
    comparison are equal. (Self-contained to avoid depending on a Mathlib lemma name.) -/
theorem eq_of_forall_gt_iff' {a b : ℝ} (H : ∀ t, a < t ↔ b < t) : a = b := by
  rcases lt_trichotomy a b with h | h | h
  · exact absurd ((H b).mp h) (lt_irrefl b)
  · exact h
  · exact absurd ((H a).mpr h) (lt_irrefl a)

/-- **Headline characterization.** The wall is blind to the vacuum at every
    threshold IFF the goal channel is separable from survival. -/
theorem wallBlind_iff_separable : WallBlind wi vac ↔ Separable wi vac := by
  constructor
  · intro h c
    exact eq_of_forall_gt_iff' (fun t => h t c)
  · intro h thr c
    rw [h c]

/-- Restated: separability is exactly the silent-blind-spot condition. -/
theorem separable_iff_wallBlind : Separable wi vac ↔ WallBlind wi vac :=
  (wallBlind_iff_separable wi vac).symm

/-- `Coupled` is the negation of `Separable`. -/
theorem coupled_iff_not_separable : Coupled wi vac ↔ ¬ Separable wi vac := by
  constructor
  · rintro ⟨c, hc⟩ hsep; exact hc (hsep c)
  · intro h
    by_contra hco
    exact h (fun c => not_not.mp (fun hne => hco ⟨c, hne⟩))

/-- **Coupling ⇒ detectability.** If the goal channel is coupled to survival, then
    there is a threshold at which the wall distinguishes the vacuumed configuration
    from its clean counterpart — the vacuum is *not* a silent blind spot. -/
theorem coupled_detectable (h : Coupled wi vac) :
    ∃ thr c, ¬ (wi (vac c) < thr ↔ wi c < thr) := by
  obtain ⟨c, hc⟩ := h
  rcases lt_or_gt_of_ne hc with hlt | hgt
  · refine ⟨wi c, c, ?_⟩
    intro hiff
    exact (lt_irrefl (wi c)) (hiff.mp hlt)
  · refine ⟨wi (vac c), c, ?_⟩
    intro hiff
    exact (lt_irrefl (wi (vac c))) (hiff.mpr hgt)

/-- A non-separable channel is detectable at some threshold (contrapositive form,
    matching the COUPLED / negative pole: vacuum can fire the wall). -/
theorem not_separable_implies_detectable (h : ¬ Separable wi vac) :
    ∃ thr c, ¬ (wi (vac c) < thr ↔ wi c < thr) :=
  coupled_detectable wi vac ((coupled_iff_not_separable wi vac).mpr h)

/-- **Positive pole.** A separable, achievable goal channel yields a *silent blind
    spot with harm*: the wall is blind to the vacuum at every threshold, AND the
    vacuum strictly degrades the goal for some configuration. -/
theorem silent_blindspot_with_harm
    (hsep : Separable wi vac) (hach : Achievable gs vac) :
    WallBlind wi vac ∧ ∃ c, gs (vac c) < gs c :=
  ⟨(wallBlind_iff_separable wi vac).mpr hsep, hach⟩

/-- **The dichotomy** (the empirical bracket, mechanized). For any system, exactly
    one holds: either the goal channel is separable (silent blind spot — positive
    pole) or it is detectable at some threshold (negative pole). -/
theorem blindspot_dichotomy :
    WallBlind wi vac ∨ (∃ thr c, ¬ (wi (vac c) < thr ↔ wi c < thr)) := by
  by_cases h : Separable wi vac
  · exact Or.inl ((wallBlind_iff_separable wi vac).mpr h)
  · exact Or.inr (not_separable_implies_detectable wi vac h)

/-! ### Non-vacuity witnesses — the definitions are inhabited (both poles realizable). -/

/-- A survival signal that ignores the goal channel is separable under any vacuum
    (the report-task survival signal: balancing reads only pole state). -/
example (s0 : ℝ) (v : ℝ → ℝ) : Separable (fun _ => s0) v := fun _ => rfl

/-- A survival signal that reads the goal channel is coupled (the cart-target
    survival signal: pursuing the target perturbs balancing). -/
example : Coupled (fun c : ℝ => c) (fun _ => (0 : ℝ)) := ⟨1, by norm_num⟩

/-- An achievable goal: vacuuming the channel strictly degrades the score. -/
example : Achievable (fun c : ℝ => c) (fun _ => (0 : ℝ)) := ⟨1, by norm_num⟩

end VacuumSeparability
end EvoEcos
