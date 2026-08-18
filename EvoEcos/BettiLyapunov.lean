/-
Betti Numbers Cannot Be Graded Lyapunov Functions
==================================================
Mechanizes the structural half of experiment_betti_lyapunov.py
(decisions.md: betti_as_lyapunov [NEGATIVE], 2026-06-10).

An integer-valued, bounded-below Lyapunov candidate (window Betti-0 of a
Markov chain trajectory) that strictly decreases while above its floor
must SATURATE: it reaches the floor within v 0 steps. After saturation it
carries no convergence-rate information — any bounded discrete observable
must identify states whose true Lyapunov distances differ (pigeonhole).

Main theorems:
  1. saturation              — strict drift above floor forces v N = 1
                               for some N ≤ v 0 (the step-45-of-2000
                               empirical finding is structural, not tuned)
  2. no_strict_drift_at_floor — at the floor the Lyapunov decrease
                               condition is unsatisfiable
  3. no_rate_information     — a discrete observable bounded by B cannot
                               separate more than B+1 states: any B+2
                               states contain two with equal observable
                               (so post-saturation, distance-to-equilibrium
                               is invisible to Betti-0)

The empirical complement (experiment, 30 seeds × 3 chains): transient
drift IS negative (H1, 27/27), saturation at step ~45/2000 with 74% of
the true Lyapunov decay still unresolved (H2), and the obstruction
certificate role survives (H4 v2: 89/90, CI [0.940, 1.000]).
-/

import Mathlib.Data.Finset.Card
import Mathlib.Combinatorics.Pigeonhole

namespace EvoEcos.BettiLyapunov

/-! ## Saturation: integer + bounded below ⟹ the floor is reached fast -/

/-- A Betti-0 trajectory `v : ℕ → ℕ` with floor 1 (a nonempty point cloud
always has at least one component) and strict Lyapunov drift above the
floor reaches the floor within `v 0` steps. This is the structural content
of the empirical saturation finding: the time-to-floor is bounded by the
INITIAL Betti number (≤ window size), not by the chain's mixing time. -/
theorem saturation (v : ℕ → ℕ)
    (h_floor : ∀ n, 1 ≤ v n)
    (h_drift : ∀ n, 1 < v n → v (n + 1) < v n) :
    ∃ N, N ≤ v 0 ∧ v N = 1 := by
  by_contra h
  push Not at h
  -- While the floor is never hit, the drift is strict at every step ≤ v 0,
  -- so v loses at least 1 per step: v k + k ≤ v 0.
  have key : ∀ k, k ≤ v 0 → v k + k ≤ v 0 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      intro hk
      have hk' : k ≤ v 0 := Nat.le_of_succ_le hk
      have h_ne : v k ≠ 1 := h k hk'
      have h_above : 1 < v k := lt_of_le_of_ne (h_floor k) (Ne.symm h_ne)
      have h_dec : v (k + 1) < v k := h_drift k h_above
      have h_ih : v k + k ≤ v 0 := ih hk'
      omega
  -- At step v 0 the budget is exhausted: v (v 0) = 0, below the floor.
  have h_end := key (v 0) le_rfl
  have h_fl := h_floor (v 0)
  omega

/-- At the floor, the strict-drift condition of a graded Lyapunov function
is unsatisfiable: `v n = 1` leaves no room below (the floor IS the small
set, and no further decrease can certify progress). -/
theorem no_strict_drift_at_floor (v : ℕ → ℕ)
    (h_floor : ∀ n, 1 ≤ v n) (n : ℕ) (h : v n = 1) :
    ¬ v (n + 1) < v n := by
  intro h_lt
  have := h_floor (n + 1)
  omega

/-! ## No rate information: bounded discrete observables cannot grade -/

/-- A discrete observable bounded by `B` (e.g. window Betti-0, which is at
most the window size) cannot distinguish more than `B + 1` states: any
`B + 2` distinct states contain two with the same observable value. In
particular, after Betti-0 saturates at 1, states at every remaining
distance-to-equilibrium are observationally identical — the observable
carries no convergence-rate information. Pigeonhole. -/
theorem no_rate_information {α : Type*} [DecidableEq α]
    (B : ℕ) (V : α → ℕ) (hB : ∀ x, V x ≤ B)
    (s : Finset α) (h_card : B + 1 < s.card) :
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ V a = V b := by
  have h_maps : ∀ a ∈ s, V a ∈ Finset.range (B + 1) := fun a _ =>
    Finset.mem_range.mpr (Nat.lt_succ_of_le (hB a))
  exact Finset.exists_ne_map_eq_of_card_lt_of_maps_to
    (by simpa using h_card) h_maps

/-- Composition: a window Betti-0 (bounded by window size `W`) saturates
within `v 0 ≤ W` steps AND is then blind among any `W + 2` states. The
two failures are the same structural fact: integer-valued + bounded means
the observable's information budget is `W + 1` values, spent during the
transient. -/
theorem saturation_then_blind {α : Type*} [DecidableEq α]
    (W : ℕ) (v : ℕ → ℕ) (V : α → ℕ)
    (h_floor : ∀ n, 1 ≤ v n)
    (h_drift : ∀ n, 1 < v n → v (n + 1) < v n)
    (hV : ∀ x, V x ≤ W)
    (s : Finset α) (h_card : W + 1 < s.card) :
    (∃ N, N ≤ v 0 ∧ v N = 1) ∧
    (∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ V a = V b) :=
  ⟨saturation v h_floor h_drift,
   no_rate_information W V hV s h_card⟩

end EvoEcos.BettiLyapunov
