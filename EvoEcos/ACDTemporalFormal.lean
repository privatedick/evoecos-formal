import EvoEcos.ACDTemporal

/-!
# ACD Temporal: Formal Monotonicity and Wall Release

**Date:** 2026-04-15

This file extends `ACDTemporal.lean` with:
1. A **kernel-refinement** condition (`MonoSetup`) requiring that later
   observations distinguish at least as many worlds as earlier ones.
2. A proof that kernel refinement yields upward-closure of architectural
   status as a direct corollary of `architectural_upward_closed`.
3. A formal definition of the **wall release time** `tStar` as the minimum
   time at which the setup becomes architectural.

## What this file proves (0 sorry)

* `mono_refines_step` — kernel refinement at each step gives `Refines`.
* `mono_refines` — kernel refinement gives `Refines` for any `t ≤ t'`.
* `architectural_upward_closed_mono` — Theorem 2: once architectural,
  stays architectural.
* `tStar_architectural` — at `tStar`, the setup is architectural.
* `tStar_min` — `tStar` is the minimum such time.
* `counterfactual_before_tStar` — before `tStar`, the setup is counterfactual.
* `architectural_after_tStar` — after `tStar`, stays architectural.
-/

namespace EvoEcos

open ObservationalSetup TemporalSetup

/-! ## Monotonic Temporal Setup -/

/--
A `MonoSetup` is a `TemporalSetup` where observations refine monotonically
in the kernel sense: at each step, equal observations at time `t+1` pull
back to equal observations at time `t`.

Formally this is the kernel containment: `ker(obs(·, t+1)) ⊆ ker(obs(·, t))`.

This models the EvoEcos wall's evidence accumulation: each time step
either preserves or sharpens the ability to distinguish worlds.
-/
structure MonoSetup (W O : Type) extends TemporalSetup W O where
  /-- Kernel refinement: equal obs at t+1 implies equal obs at t. -/
  mono : ∀ (t : Nat) (w1 w2 : W),
    toTemporalSetup.obs w1 (t + 1) = toTemporalSetup.obs w2 (t + 1) →
    toTemporalSetup.obs w1 t = toTemporalSetup.obs w2 t

namespace MonoSetup

variable {W O : Type} (S : MonoSetup W O)

/-- The underlying TemporalSetup. -/
def ts : TemporalSetup W O := S.toTemporalSetup

/-- Architectural status at time t. -/
abbrev ArchitecturalAt (t : Nat) : Prop :=
  (ts S).ArchitecturalAt t

/-- Counterfactual status at time t. -/
abbrev CounterfactualAt (t : Nat) : Prop :=
  (ts S).CounterfactualAt t

/-! ## Monotonicity implies Refinement Preorder -/

/--
At each step, the kernel mono condition directly gives `Refines`.
-/
theorem mono_refines_step (t : Nat) :
    (ts S).Refines t (t + 1) :=
  S.mono t

/-- Kernel refinement gives `Refines` for any `t ≤ t'`. -/
theorem mono_refines {t1 t2 : Nat} (hle : t1 ≤ t2) :
    (ts S).Refines t1 t2 := by
  intro w1 w2 hobs
  -- Chain from obs equality at t2 down to t1 via mono at each step.
  -- Motive P n (hn : t1 ≤ n) := obs w1 n = obs w2 n → obs w1 t1 = obs w2 t1
  -- Base (n = t1): identity. Step (n → n+1): mono pulls back equality.
  refine Nat.le_induction
    (P := fun n _ => (ts S).obs w1 n = (ts S).obs w2 n →
                     (ts S).obs w1 t1 = (ts S).obs w2 t1)
    (fun h => h)
    (fun n _ ih hn => ih (S.mono n w1 w2 hn))
    t2 hle hobs

/-! ## Theorem 2: Architectural is Upward-Closed -/

/--
**Theorem 2 (Upward Closure).** If the setup is architectural at time `t`
and `t ≤ t'`, then it is architectural at time `t'`.

Interpretation: once evidence has accumulated enough to determine truth
for all worlds sharing the same observation, additional evidence cannot
break this determination. More information cannot create ambiguity.
-/
theorem architectural_upward_closed_mono {t t' : Nat}
    (hArch : S.ArchitecturalAt t)
    (hle : t ≤ t') :
    S.ArchitecturalAt t' := by
  -- Rewrite t' as t + k for some k
  obtain ⟨k, hk⟩ : ∃ k, t' = t + k := ⟨t' - t, (Nat.add_sub_of_le hle).symm⟩
  subst hk
  exact architectural_upward_closed (ts S) hArch (mono_refines S (Nat.le_add_right t k))

/-! ## Theorem 4: Wall Release Time -/

/--
The wall release time: the earliest time at which the setup becomes
architectural.

In EvoEcos terms, this is the moment when accumulated evidence is
sufficient to determine truth for all worlds sharing the same
observation history. Before this time, the L2 wall should remain active.

The value requires a witness that some architectural time exists.
Not all setups eventually become architectural — some predicates remain
counterfactual regardless of observation accumulation (ACD obstacle 1).
-/
noncomputable def tStar (hWitness : ∃ t, S.ArchitecturalAt t) : Nat :=
  @Nat.find (fun t => S.ArchitecturalAt t)
    (fun t => Classical.propDecidable (S.ArchitecturalAt t))
    hWitness

/--
`tStar` is architectural.
-/
theorem tStar_architectural (hWitness : ∃ t, S.ArchitecturalAt t) :
    S.ArchitecturalAt (S.tStar hWitness) :=
  @Nat.find_spec (fun t => S.ArchitecturalAt t)
    (fun t => Classical.propDecidable (S.ArchitecturalAt t))
    hWitness

/--
`tStar` is the minimum architectural time: no earlier time is architectural.
-/
theorem tStar_min (hWitness : ∃ t, S.ArchitecturalAt t) (m : Nat)
    (hlt : m < S.tStar hWitness) :
    ¬ S.ArchitecturalAt m :=
  @Nat.find_min (fun t => S.ArchitecturalAt t)
    (fun t => Classical.propDecidable (S.ArchitecturalAt t))
    hWitness m hlt

/--
If the setup eventually becomes architectural, then `tStar` satisfies
the characteristic property: architectural at `tStar`, counterfactual before.
-/
theorem tStar_spec (hWitness : ∃ t, S.ArchitecturalAt t) :
    S.ArchitecturalAt (S.tStar hWitness) ∧
    ∀ t' : Nat, t' < S.tStar hWitness → ¬ S.ArchitecturalAt t' :=
  ⟨tStar_architectural S hWitness, fun t' => tStar_min S hWitness t'⟩

/--
Before `tStar`, the setup is counterfactual.
-/
theorem counterfactual_before_tStar (hWitness : ∃ t, S.ArchitecturalAt t)
    {t : Nat} (hlt : t < S.tStar hWitness) :
    S.CounterfactualAt t := by
  have hNotArch : ¬ S.ArchitecturalAt t := tStar_min S hWitness t hlt
  change (ts S).CounterfactualAt t
  change ¬ (ts S).ArchitecturalAt t at hNotArch
  -- ¬Architectural ↔ ¬(¬Counterfactual) ↔ Counterfactual
  by_contra hNotCF
  have : (ts S).ArchitecturalAt t :=
    (architectural_iff_not_counterfactual ((ts S).atTime t)).mpr hNotCF
  exact hNotArch this

/--
After `tStar`, the setup remains architectural (upward closure).
-/
theorem architectural_after_tStar (hWitness : ∃ t, S.ArchitecturalAt t)
    (t : Nat) (hge : t ≥ S.tStar hWitness) :
    S.ArchitecturalAt t :=
  architectural_upward_closed_mono S (tStar_architectural S hWitness) hge

/-! ## Wall Commitment Policy -/

/--
The temporal wall theorem: commit at time `t` iff architectural at time `t`.
-/
theorem wall_commit_policy (t : Nat) :
    S.ArchitecturalAt t ↔ ¬ S.CounterfactualAt t :=
  architectural_iff_not_counterfactual ((ts S).atTime t)

/--
Corollary: the wall should be active before `tStar`.

    wall_active(t) ⟺ t < tStar
-/
theorem wall_active_iff_before_tStar (hWitness : ∃ t, S.ArchitecturalAt t)
    (t : Nat) :
    t < S.tStar hWitness ↔ S.CounterfactualAt t :=
  ⟨counterfactual_before_tStar S hWitness, fun hCF => by
    by_contra hge
    have hArch := architectural_after_tStar S hWitness t (Nat.le_of_not_gt hge)
    exact (wall_commit_policy S t).mp hArch hCF⟩

end MonoSetup

end EvoEcos
