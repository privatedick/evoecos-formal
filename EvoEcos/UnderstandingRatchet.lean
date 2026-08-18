import EvoEcos.Layers
import EvoEcos.L3Understanding

/-!
# UnderstandingRatchet — the positive counterpart to the wall theorems

The wall corpus proves the system *does not collapse* (`Invariants`) and
*recovers from danger* (`WallFiniteTimeRecovery`, `WallLiveness`). Every one of
those guarantees is defensive: nothing bad happens, danger is temporary, the
brake works. None of them states that the system ever *gets anywhere*.

This file proves the missing half: L3 understanding **accumulates and is never
lost**. Capability ratchets up. The wall pauses accrual during danger; it does
not erase what was already understood.

Dynamics (verbatim from `EvoEcos.Layers`):
* `L3State.plan s l2` increases `understanding` by `1/100`, capped at `1`,
  exactly when `s.active ∧ ¬s.blocked ∧ ¬l2.wall`; otherwise it is unchanged.
* `L3State.blockWhenWallActive s l2` sets `blocked` when the wall is up, and
  never touches `understanding`.

Main results (0 sorry, 0 axiom):
* `plan_nondecreasing`     — a planning step never decreases understanding.
* `block_preserves`        — wall-blocking never changes understanding.
* `tick_nondecreasing`     — a full L3 tick (block, then plan) never decreases it.
* `understanding_monotone` — over ANY sequence of ticks (any wall pattern at all),
                             final understanding ≥ initial. The wall pauses
                             progress; it never reverses it.
* `productive_step`        — a safe, active, unblocked step adds exactly `1/100`
                             (below the cap): strict, quantified progress.
* `reaches_max`            — after 100 productive steps, understanding = 1,
                             from any nonnegative starting point. Sustained
                             safety ⇒ the system converges to full understanding.
-/

namespace EvoEcos
namespace L3State

/-! ## Single-step facts -/

/-- A planning step never decreases understanding: it either adds a capped
    nonnegative increment (in the productive branch) or leaves it unchanged. -/
theorem plan_nondecreasing (s : L3State) (l2 : L2State) :
    s.understanding.val ≤ (plan s l2).understanding.val := by
  unfold plan
  split
  · -- productive: understanding := ⟨min 1 (val + 1/100), _⟩
    show s.understanding.val ≤ min 1 (s.understanding.val + (1 / 100 : ℝ))
    apply le_min
    · exact s.understanding.property.2
    · linarith
  · -- unchanged
    exact le_refl _

/-- Wall-blocking never changes understanding — it only flips `blocked`. -/
theorem block_preserves (s : L3State) (l2 : L2State) :
    (blockWhenWallActive s l2).understanding = s.understanding := by
  unfold blockWhenWallActive
  split <;> rfl

/-- Planning preserves the `active` flag (it only edits `understanding`). -/
theorem plan_active (s : L3State) (l2 : L2State) :
    (plan s l2).active = s.active := by
  unfold plan; split <;> rfl

/-- Planning preserves the `blocked` flag. -/
theorem plan_blocked (s : L3State) (l2 : L2State) :
    (plan s l2).blocked = s.blocked := by
  unfold plan; split <;> rfl

/-! ## One full tick: the wall acts, then L3 attempts to plan -/

/-- A full L3 tick: the wall blocks L3 if active, then L3 attempts a planning
    step (which is a no-op unless safe and unblocked). This is the real
    per-step L3 dynamics. -/
noncomputable def tick (s : L3State) (l2 : L2State) : L3State :=
  plan (blockWhenWallActive s l2) l2

/-- A full tick never decreases understanding. -/
theorem tick_nondecreasing (s : L3State) (l2 : L2State) :
    s.understanding.val ≤ (tick s l2).understanding.val := by
  unfold tick
  have hb : (blockWhenWallActive s l2).understanding.val = s.understanding.val := by
    rw [block_preserves]
  rw [← hb]
  exact plan_nondecreasing _ _

/-! ## The ratchet: monotonicity over any trajectory -/

/-- Run a sequence of ticks, one per wall-state in the list. -/
noncomputable def run (s : L3State) : List L2State → L3State
  | [] => s
  | l2 :: rest => run (tick s l2) rest

/-- **The ratchet.** Over any sequence of ticks — any wall pattern whatsoever —
    final understanding is at least initial understanding. The wall can pause
    accrual arbitrarily often; it can never claw it back. -/
theorem understanding_monotone (s : L3State) (ws : List L2State) :
    s.understanding.val ≤ (run s ws).understanding.val := by
  induction ws generalizing s with
  | nil => simp [run]
  | cons l2 rest ih =>
    simp only [run]
    exact le_trans (tick_nondecreasing s l2) (ih (tick s l2))

/-! ## Quantified progress and convergence under sustained safety -/

/-- A productive step (safe, active, unblocked) adds exactly `1/100`, capped at
    `1`. This is the strict-progress lemma: below the cap, understanding rises. -/
theorem productive_step (s : L3State) (l2 : L2State)
    (ha : s.active = true) (hb : s.blocked = false) (hw : l2.wall = false) :
    (plan s l2).understanding.val = min 1 (s.understanding.val + (1 / 100 : ℝ)) := by
  unfold plan
  split
  · rfl
  · rename_i hcond
    exact absurd ⟨ha, by simp [hb], by simp [hw]⟩ hcond

/-- Iterate `plan` against a fixed safe wall-state `n` times. -/
noncomputable def planN (l2 : L2State) : Nat → L3State → L3State
  | 0, s => s
  | n + 1, s => plan (planN l2 n s) l2

/-- Iterating `plan` preserves `active`. -/
theorem planN_active (l2 : L2State) (n : Nat) (s : L3State) :
    (planN l2 n s).active = s.active := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [planN]; rw [plan_active]; exact ih

/-- Iterating `plan` preserves `blocked`. -/
theorem planN_blocked (l2 : L2State) (n : Nat) (s : L3State) :
    (planN l2 n s).blocked = s.blocked := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [planN]; rw [plan_blocked]; exact ih

/-- After `n` productive steps, understanding is at least `min 1 (u₀ + n/100)`:
    each safe step adds `1/100` until the cap. -/
theorem planN_lower (l2 : L2State) (n : Nat) (s : L3State)
    (ha : s.active = true) (hb : s.blocked = false) (hw : l2.wall = false) :
    min 1 (s.understanding.val + (n : ℝ) / 100) ≤ (planN l2 n s).understanding.val := by
  induction n with
  | zero =>
    simp only [planN, Nat.cast_zero]
    have h2 := s.understanding.property.2
    have hz : s.understanding.val + (0 : ℝ) / 100 = s.understanding.val := by ring
    rw [hz]
    exact min_le_right _ _
  | succ n ih =>
    have hpa : (planN l2 n s).active = true := by rw [planN_active]; exact ha
    have hpb : (planN l2 n s).blocked = false := by rw [planN_blocked]; exact hb
    have hstep : (planN l2 (n + 1) s).understanding.val
        = min 1 ((planN l2 n s).understanding.val + (1 / 100 : ℝ)) := by
      simp only [planN]
      exact productive_step (planN l2 n s) l2 hpa hpb hw
    rw [hstep]
    have hv1 : (planN l2 n s).understanding.val ≤ 1 :=
      (planN l2 n s).understanding.property.2
    rcases lt_or_ge (s.understanding.val + (n : ℝ) / 100) 1 with hc | hc
    · -- below the cap: the bound advances by exactly 1/100
      rw [min_eq_right (le_of_lt hc)] at ih
      apply min_le_min (le_refl 1)
      push_cast
      linarith
    · -- already at the cap: prior understanding is 1, stays 1
      rw [min_eq_left hc] at ih
      have hv_eq : (planN l2 n s).understanding.val = 1 := le_antisymm hv1 ih
      rw [hv_eq, min_eq_left (by norm_num : (1 : ℝ) ≤ 1 + 1 / 100)]
      exact min_le_left _ _

/-- **Convergence under sustained safety.** From any nonnegative starting point,
    100 productive steps drive understanding to its maximum, `1`. The system does
    not merely avoid collapse — given safety, it provably arrives. -/
theorem reaches_max (l2 : L2State) (s : L3State)
    (ha : s.active = true) (hb : s.blocked = false) (hw : l2.wall = false) :
    (planN l2 100 s).understanding.val = 1 := by
  have hlow := planN_lower l2 100 s ha hb hw
  have hu0 : (0 : ℝ) ≤ s.understanding.val := s.understanding.property.1
  have hcap : min (1 : ℝ) (s.understanding.val + (100 : ℕ) / 100) = 1 := by
    apply min_eq_left
    push_cast
    linarith
  rw [hcap] at hlow
  have hle := (planN l2 100 s).understanding.property.2
  linarith

end L3State
end EvoEcos
