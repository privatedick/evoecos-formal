import EvoEcos.UnderstandingRatchet
import EvoEcos.MetaLearningUnlock
import EvoEcos.WallFiniteTimeRecovery

/-!
# StableGrowthCycle — the keystone tying the defensive corpus to the generative spine

This composes the three load-bearing results into one end-to-end guarantee about
a full **danger → recovery → growth** cycle:

* `WallFiniteTimeRecovery.finite_recovery_exists` — when L1 stability drops below
  the wall threshold, the wall guarantees recovery to threshold in finite time
  (the *defensive* corpus: danger is always temporary).
* `UnderstandingRatchet` — across the entire wall-up interval, L3 understanding is
  *exactly preserved* (the wall blocks new planning, never erases old understanding),
  and once safety returns, sustained planning drives understanding to full.
* `MetaLearningUnlock` — that recovered, full understanding then unlocks L4
  meta-learning.

Read together: **the system survives danger, loses nothing it understood while it
was defending itself, and resumes compounding — all the way up to unlocking the
layer above.** The wall is not a cage. It is what makes durable growth safe.

Main results (0 sorry, 0 axiom):
* `tick_blocked_preserves` — a tick with the wall up preserves understanding exactly.
* `run_blocked_preserves`  — an entire wall-up interval preserves understanding exactly.
* `stable_growth_cycle`    — the keystone: finite recovery ∧ no understanding lost
                             across the danger interval ∧ post-recovery growth reaches
                             full understanding and unlocks L4.
-/

open WallFiniteTimeRecovery WallCostBenefit

namespace EvoEcos
namespace L3State

/-- A planning step on an already-blocked L3 is a no-op on understanding:
    the wall has L3 paused, so no new understanding accrues — but none is lost. -/
theorem plan_blocked_noop (s : L3State) (l2 : L2State) (hb : s.blocked = true) :
    (plan s l2).understanding = s.understanding := by
  unfold plan
  rw [if_neg (by simp [hb])]

/-- A full tick with the wall up preserves understanding exactly: the wall blocks
    L3, the blocked planning step does nothing, understanding is conserved. -/
theorem tick_blocked_preserves (s : L3State) (l2 : L2State) (hw : l2.wall = true) :
    (tick s l2).understanding = s.understanding := by
  unfold tick
  have hblk : (blockWhenWallActive s l2).blocked = true := by
    unfold blockWhenWallActive; rw [if_pos hw]
  rw [plan_blocked_noop _ l2 hblk, block_preserves]

/-- Wall-blocking preserves the `active` flag. -/
theorem block_active (s : L3State) (l2 : L2State) :
    (blockWhenWallActive s l2).active = s.active := by
  unfold blockWhenWallActive; split <;> rfl

/-- A full tick preserves the `active` flag (block and plan both do). -/
theorem tick_active (s : L3State) (l2 : L2State) :
    (tick s l2).active = s.active := by
  unfold tick; rw [plan_active, block_active]

/-- An entire interval of ticks preserves the `active` flag. -/
theorem run_active : ∀ (ws : List L2State) (s : L3State),
    (run s ws).active = s.active
  | [], _ => rfl
  | l2 :: rest, s => by
      simp only [run]
      rw [run_active rest (tick s l2), tick_active]

/-- Over an entire wall-up interval (every step has the wall active), understanding
    is preserved exactly. Nothing the system understood is lost while it defends L1. -/
theorem run_blocked_preserves : ∀ (ws : List L2State) (s : L3State),
    (∀ l2 ∈ ws, l2.wall = true) →
    (run s ws).understanding = s.understanding
  | [], s, _ => by simp [run]
  | l2 :: rest, s, hall => by
      simp only [run]
      have hw : l2.wall = true := hall l2 (by simp)
      have hrest : ∀ x ∈ rest, x.wall = true := fun x hx => hall x (by simp [hx])
      rw [run_blocked_preserves rest (tick s l2) hrest, tick_blocked_preserves s l2 hw]

/-- When the wall lifts, L3 is unblocked. This is an exact mirror of the runtime's
    `_deactivate_wall_atomically` (stable_bootstrap_arch.py:1188-1189), which sets
    `l3_wall_active = False` and `l3_blocked = False` atomically (TLA+ L2DeactivateWall).
    It clears only `blocked`; the `active` flag is carried through untouched. -/
def resume (s : L3State) : L3State := { s with blocked := false }

@[simp] theorem resume_understanding (s : L3State) :
    (resume s).understanding = s.understanding := rfl

@[simp] theorem resume_active (s : L3State) : (resume s).active = s.active := rfl

@[simp] theorem resume_blocked (s : L3State) : (resume s).blocked = false := rfl

end L3State

/-- **The keystone.** A full danger → recovery → growth cycle:

1. **Recovery (defensive).** With L1 stability `sL1` below the wall threshold and
   the wall in its feasible zone (`p < r1/h`), recovery to threshold is guaranteed
   in finite time.
2. **No loss (ratchet).** Across the entire wall-up danger interval `dangerWalls`,
   L3 understanding is preserved exactly — the wall paused growth, it did not undo it.
3. **Resumed growth + unlock (generative).** Once safe (`l2safe.wall = false`) and
   L3 resumes, 100 productive steps drive understanding to full, which makes an
   active L4's observation productive — meta-learning is unlocked.

The system defends itself, keeps everything it learned, and compounds upward. -/
theorem stable_growth_cycle
    (l2safe : L2State) (s : L3State) (l4 : L4State)
    (dangerWalls : List L2State)
    (hdanger : ∀ l2 ∈ dangerWalls, l2.wall = true)
    (hactive : s.active = true)
    (hsafe : l2safe.wall = false)
    (hl4 : l4.active = true)
    (sL1 p : ℝ) (hs0 : 0 ≤ sL1) (hs : sL1 < wall_act_threshold)
    (hp0 : 0 ≤ p) (hp : p < r1 / h) :
    -- (1) recovery from danger is guaranteed in finite time
    (∃ T : ℕ, sL1 + (T : ℝ) * (r1 - p * h) ≥ wall_act_threshold)
    -- (2) no understanding is lost across the entire wall-up danger interval
    ∧ (L3State.run s dangerWalls).understanding.val = s.understanding.val
    -- (3) once safe, sustained planning reaches full understanding and unlocks L4
    ∧ (l4.observe (L3State.planN l2safe 100 (L3State.resume (L3State.run s dangerWalls)))
        ).hypothesisQualityThreshold.val
        = min 1 (l4.hypothesisQualityThreshold.val + l4.learningRate.val) := by
  refine ⟨?_, ?_, ?_⟩
  · -- defensive: finite recovery (WallFiniteTimeRecovery)
    exact finite_recovery_exists sL1 p hs0 hs hp0 hp
  · -- ratchet: understanding preserved across the wall-up interval
    rw [L3State.run_blocked_preserves dangerWalls s hdanger]
  · -- generative: resumed growth reaches full understanding and unlocks L4
    have hresume_active : (L3State.resume (L3State.run s dangerWalls)).active = true := by
      rw [L3State.resume_active, L3State.run_active]; exact hactive
    exact ratchet_unlocks_metalearning l2safe (L3State.resume (L3State.run s dangerWalls)) l4
      hresume_active (L3State.resume_blocked _) hsafe hl4

end EvoEcos
