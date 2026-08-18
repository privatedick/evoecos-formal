import EvoEcos.ACD

/-!
# ACD Extension: Adversarial Robustness

**Date:** 2026-04-15

An adversary who can perturb worlds via `adv : W → W` creates an effective
setup where observation is `obs ∘ adv` but truth remains original.

## What this file proves (0 sorry)

* `adversarial_force_counterfactual` — non-constant truth ⇒ adversary can force CF.
* `robust_iff_constant` — robust iff truth is constant.
* `constant_implies_robust` — constant truth is always robust.
* `bounded_robust_singleton` — bounded adversaries allow non-trivial robustness.

-/

namespace EvoEcos

open ObservationalSetup

/-! ## Adversarial Perturbation -/

/--
An adversarial perturbation replaces each world with another. The effective
observation is obs ∘ adv but truth stays original.
-/
def AdversarialSetup {W O : Type} (S : ObservationalSetup W O) (adv : W → W) :
    ObservationalSetup W O where
  obs   := fun w => S.obs (adv w)
  truth := S.truth

/--
A setup is adversarially robust iff it remains architectural under every
possible world perturbation.
-/
def AdversariallyRobust {W O : Type} (S : ObservationalSetup W O) : Prop :=
  ∀ adv : W → W, Architectural (AdversarialSetup S adv)

/--
Truth predicate is constant (same value on every world).
-/
def TruthConstant {W O : Type} (S : ObservationalSetup W O) : Prop :=
  ∃ b : Bool, ∀ w : W, S.truth w = b

/-! ## Main Results -/

/--
If truth is constant then the setup is adversarially robust.
-/
theorem constant_implies_robust {W O : Type} (S : ObservationalSetup W O)
    (hc : TruthConstant S) : AdversariallyRobust S := by
  obtain ⟨b, hb⟩ := hc
  intro adv w1 w2 _
  exact (hb w1).trans (hb w2).symm

/--
If truth is non-constant, the adversary can force counterfactual
by mapping all worlds to a single fixed world.
-/
theorem adversarial_force_counterfactual {W O : Type} (S : ObservationalSetup W O)
    [Nonempty W]
    (hnc : ¬ TruthConstant S) :
    ∃ adv : W → W, Counterfactual (AdversarialSetup S adv) := by
  have hne : ∃ w1 w2, S.truth w1 ≠ S.truth w2 := by
    by_contra h
    push_neg at h
    have : TruthConstant S := ⟨S.truth (Nonempty.some ‹_›), fun w => (h (Nonempty.some ‹_›) w).symm⟩
    exact hnc this
  obtain ⟨w1, w2, hne⟩ := hne
  -- Map all worlds to w1. Then all observations collapse to obs(w1).
  -- But truth(w1) ≠ truth(w2), so counterfactual.
  refine ⟨fun _ => w1, w1, w2, rfl, hne⟩

/--
A setup is adversarially robust iff truth is constant.
-/
theorem robust_iff_constant {W O : Type} (S : ObservationalSetup W O)
    [Nonempty W] :
    AdversariallyRobust S ↔ TruthConstant S := by
  constructor
  · intro h
    by_contra hnc
    obtain ⟨adv, hcf⟩ := adversarial_force_counterfactual S hnc
    have := h adv
    rw [architectural_iff_not_counterfactual] at this
    exact this hcf
  · exact constant_implies_robust S

/-! ## Bounded Adversaries -/

/--
A bounded adversary can only perturb within permitted set P.
-/
def BoundedAdversary {W O : Type} (S : ObservationalSetup W O)
    (P : W → Set W) (adv : W → W) : Prop :=
  ∀ w : W, adv w ∈ P w

/--
Robustness against bounded adversaries.
-/
def BoundedRobust {W O : Type} (S : ObservationalSetup W O) (P : W → Set W) : Prop :=
  ∀ adv : W → W, BoundedAdversary S P adv → Architectural (AdversarialSetup S adv)

/--
Singleton-bounded adversary: can only pick the world itself.
-/
theorem bounded_robust_singleton {W O : Type} (S : ObservationalSetup W O)
    (hArch : Architectural S) :
    BoundedRobust S (fun w => {w}) := by
  intro adv hbd w1 w2 hobs
  simp only [AdversarialSetup] at hobs
  have h1 : adv w1 = w1 := by have := hbd w1; simp at this; exact this
  have h2 : adv w2 = w2 := by have := hbd w2; simp at this; exact this
  rw [h1, h2] at hobs
  exact hArch w1 w2 hobs

end EvoEcos
