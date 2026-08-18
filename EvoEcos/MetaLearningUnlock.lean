import EvoEcos.Layers
import EvoEcos.UnderstandingRatchet

/-!
# MetaLearningUnlock — accumulated understanding turns on the layer above it

`UnderstandingRatchet` proved L3 understanding accumulates and is never lost
(progress points *sideways*, through time). This file points *upward*: the
understanding L3 has banked **unlocks L4 meta-learning**.

`L4State.observe` (from `EvoEcos.Layers`) raises L4's hypothesis-quality
threshold by `learningRate` (capped at 1) — but only when L4 is active and
`l3.understanding.val ≥ 0.8`. So L4 cannot improve on its own; it improves
*because* L3 has understood enough. The layers build on each other rather than
merely gating each other.

Main results (0 sorry, 0 axiom):
* `observe_nondecreasing` — an observation step never lowers L4's quality threshold.
* `observe_productive`    — when L3 understanding ≥ 0.8 and L4 is active, observing
                            raises the threshold by exactly `min 1 (q + rate)`.
* `observe_strict`        — below the cap and with positive learning rate, that
                            increase is strict: real meta-learning progress.
* `ratchet_unlocks_metalearning` — the capstone. Running L3 to full understanding
                            (`reaches_max`) makes an L4 observation productive:
                            L3's accrued understanding is exactly what switches L4 on.

The single-step L4 facts above leave the *upward* ratchet shallower than the
*sideways* (L3) one in `UnderstandingRatchet`, which has single-step → trajectory
→ convergence. We close that asymmetry so both layers are ratchets at equal depth:
* `observe_monotone`        — over ANY sequence of observations (any understanding
                              pattern), L4's quality threshold never drops.
* `observe_productive_lower`— `n` productive observations give ≥ `min 1 (q₀ + n·rate)`.
* `reaches_max_quality`     — for any positive learning rate, finitely many
                              productive observations drive L4 quality to its cap `1`.
* `cognitive_state_monotone`— the two-axis capstone: neither layer ever regresses.
-/

namespace EvoEcos
namespace L4State

/-- An observation step never lowers L4's hypothesis-quality threshold. -/
theorem observe_nondecreasing (s : L4State) (l3 : L3State) :
    s.hypothesisQualityThreshold.val ≤ (observe s l3).hypothesisQualityThreshold.val := by
  unfold observe
  split
  · show s.hypothesisQualityThreshold.val
        ≤ min 1 (s.hypothesisQualityThreshold.val + s.learningRate.val)
    apply le_min
    · exact s.hypothesisQualityThreshold.property.2
    · linarith [s.learningRate.property.1]
  · exact le_refl _

/-- When L4 is active and L3 understanding has reached ≥ 0.8, an observation
    step raises the quality threshold by exactly `min 1 (q + rate)`. This is the
    quantified unlock: high understanding ⇒ measurable meta-learning gain. -/
theorem observe_productive (s : L4State) (l3 : L3State)
    (ha : s.active = true) (hu : l3.understanding.val ≥ 0.8) :
    (observe s l3).hypothesisQualityThreshold.val
      = min 1 (s.hypothesisQualityThreshold.val + s.learningRate.val) := by
  unfold observe
  split
  · rfl
  · rename_i hcond
    exact absurd ⟨ha, hu⟩ hcond

/-- Below the cap and with a positive learning rate, the unlock is a *strict*
    increase — L4 genuinely advances, it does not merely fail to regress. -/
theorem observe_strict (s : L4State) (l3 : L3State)
    (ha : s.active = true) (hu : l3.understanding.val ≥ 0.8)
    (hrate : 0 < s.learningRate.val)
    (hroom : s.hypothesisQualityThreshold.val + s.learningRate.val ≤ 1) :
    s.hypothesisQualityThreshold.val < (observe s l3).hypothesisQualityThreshold.val := by
  rw [observe_productive s l3 ha hu, min_eq_right hroom]
  linarith

/-! ## Trajectory and convergence: the upward ratchet at full depth

`UnderstandingRatchet` gives the L3 side three layers of guarantee — single step,
whole trajectory, convergence to the cap. The lemmas above give L4 only the single
step. We now close that asymmetry: over any observation sequence L4's quality
threshold never drops, and under repeated unlock it converges to its cap. Both
layers are ratchets at equal depth. -/

/-- `observe` preserves `active` — it only ever edits `hypothesisQualityThreshold`. -/
theorem observe_active (s : L4State) (l3 : L3State) :
    (observe s l3).active = s.active := by
  unfold observe; split <;> rfl

/-- `observe` preserves `learningRate`. -/
theorem observe_learningRate (s : L4State) (l3 : L3State) :
    (observe s l3).learningRate = s.learningRate := by
  unfold observe; split <;> rfl

/-- Observe a sequence of L3 states. -/
noncomputable def observeSeq (l4 : L4State) : List L3State → L4State
  | [] => l4
  | l3 :: rest => observeSeq (observe l4 l3) rest

/-- **The upward ratchet, trajectory form.** No matter what sequence of L3 states
    L4 observes — high-understanding, low, interleaved — its quality threshold never
    drops. The strict-increase branch needs high understanding; the no-op branch
    leaves quality untouched. Either way, accrual is monotone. Mirrors
    `L3State.understanding_monotone`. -/
theorem observe_monotone (l4 : L4State) (l3s : List L3State) :
    l4.hypothesisQualityThreshold.val ≤ (observeSeq l4 l3s).hypothesisQualityThreshold.val := by
  induction l3s generalizing l4 with
  | nil => simp [observeSeq]
  | cons l3 rest ih =>
    simp only [observeSeq]
    exact le_trans (observe_nondecreasing l4 l3) (ih (observe l4 l3))

/-- Iterate `observe` against a fixed high-understanding L3 state, `n` times. -/
noncomputable def observeProductiveN (l4 : L4State) (l3 : L3State) : Nat → L4State
  | 0 => l4
  | n + 1 => observe (observeProductiveN l4 l3 n) l3

theorem observeProductiveN_active (l4 : L4State) (l3 : L3State) (n : Nat) :
    (observeProductiveN l4 l3 n).active = l4.active := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [observeProductiveN]; rw [observe_active]; exact ih

theorem observeProductiveN_learningRate (l4 : L4State) (l3 : L3State) (n : Nat) :
    (observeProductiveN l4 l3 n).learningRate.val = l4.learningRate.val := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [observeProductiveN]; rw [observe_learningRate]; exact ih

/-- After `n` productive observations (L4 active, L3 understanding ≥ 0.8), the
    quality threshold is at least `min 1 (q₀ + n·rate)` — each unlock adds `rate`
    until the cap. Mirrors `L3State.planN_lower`. -/
theorem observe_productive_lower (l4 : L4State) (l3 : L3State)
    (ha : l4.active = true) (hu : l3.understanding.val ≥ 0.8) (n : Nat) :
    min 1 (l4.hypothesisQualityThreshold.val + (n : ℝ) * l4.learningRate.val)
      ≤ (observeProductiveN l4 l3 n).hypothesisQualityThreshold.val := by
  induction n with
  | zero =>
    simp only [observeProductiveN, Nat.cast_zero]
    have hz : l4.hypothesisQualityThreshold.val + (0 : ℝ) * l4.learningRate.val
        = l4.hypothesisQualityThreshold.val := by ring
    rw [hz]
    exact min_le_right _ _
  | succ n ih =>
    have hpa : (observeProductiveN l4 l3 n).active = true := by
      rw [observeProductiveN_active]; exact ha
    have hpr : (observeProductiveN l4 l3 n).learningRate.val = l4.learningRate.val :=
      observeProductiveN_learningRate l4 l3 n
    have hstep : (observeProductiveN l4 l3 (n + 1)).hypothesisQualityThreshold.val
        = min 1 ((observeProductiveN l4 l3 n).hypothesisQualityThreshold.val
                   + l4.learningRate.val) := by
      simp only [observeProductiveN]
      rw [← hpr]
      exact observe_productive (observeProductiveN l4 l3 n) l3 hpa hu
    rw [hstep]
    have hv1 : (observeProductiveN l4 l3 n).hypothesisQualityThreshold.val ≤ 1 :=
      (observeProductiveN l4 l3 n).hypothesisQualityThreshold.property.2
    rcases lt_or_ge (l4.hypothesisQualityThreshold.val + (n : ℝ) * l4.learningRate.val) 1
      with hc | hc
    · -- below the cap: the bound advances by exactly `rate`
      rw [min_eq_right (le_of_lt hc)] at ih
      apply min_le_min (le_refl 1)
      push_cast
      linarith
    · -- already at the cap: prior quality is 1, stays 1
      rw [min_eq_left hc] at ih
      have hv_eq : (observeProductiveN l4 l3 n).hypothesisQualityThreshold.val = 1 :=
        le_antisymm hv1 ih
      rw [hv_eq, min_eq_left (by linarith [l4.learningRate.property.1] :
            (1 : ℝ) ≤ 1 + l4.learningRate.val)]
      exact min_le_left _ _

/-- **Convergence under repeated unlock.** For any positive learning rate, finitely
    many productive observations drive L4's quality threshold to its cap `1`. L4
    does not merely avoid regression — given sustained high understanding, it
    provably arrives. Mirrors `L3State.reaches_max`, but parameterized by `rate`
    rather than fixed at the `1/100` understanding step. -/
theorem reaches_max_quality (l4 : L4State) (l3 : L3State)
    (ha : l4.active = true) (hu : l3.understanding.val ≥ 0.8)
    (hrate : 0 < l4.learningRate.val) :
    ∃ n : ℕ, (observeProductiveN l4 l3 n).hypothesisQualityThreshold.val = 1 := by
  -- pick n with (1 - q₀)/rate ≤ n  (Archimedean); then q₀ + n·rate ≥ 1
  obtain ⟨n, hn⟩ :=
    exists_nat_ge ((1 - l4.hypothesisQualityThreshold.val) / l4.learningRate.val)
  have h1 : 1 ≤ l4.hypothesisQualityThreshold.val + (n : ℝ) * l4.learningRate.val := by
    have hkey : 1 - l4.hypothesisQualityThreshold.val ≤ (n : ℝ) * l4.learningRate.val :=
      (div_le_iff₀ hrate).mp hn
    linarith
  refine ⟨n, ?_⟩
  have hlow := observe_productive_lower l4 l3 ha hu n
  have hcap :
      min 1 (l4.hypothesisQualityThreshold.val + (n : ℝ) * l4.learningRate.val) = 1 := by
    apply min_eq_left; exact h1
  rw [hcap] at hlow
  have hle : (observeProductiveN l4 l3 n).hypothesisQualityThreshold.val ≤ 1 :=
    (observeProductiveN l4 l3 n).hypothesisQualityThreshold.property.2
  linarith

end L4State

/-- **Capstone: the ratchet unlocks meta-learning.** Drive L3 to full
    understanding via 100 productive steps (`UnderstandingRatchet.reaches_max`);
    that accrued understanding makes an active L4's observation productive. The
    understanding L3 banked is precisely what switches the layer above it on. -/
theorem ratchet_unlocks_metalearning (l2 : L2State) (s : L3State) (l4 : L4State)
    (ha : s.active = true) (hb : s.blocked = false) (hw : l2.wall = false)
    (hl4 : l4.active = true) :
    (l4.observe (L3State.planN l2 100 s)).hypothesisQualityThreshold.val
      = min 1 (l4.hypothesisQualityThreshold.val + l4.learningRate.val) := by
  have hmax : (L3State.planN l2 100 s).understanding.val = 1 :=
    L3State.reaches_max l2 s ha hb hw
  have hu : (L3State.planN l2 100 s).understanding.val ≥ 0.8 := by rw [hmax]; norm_num
  exact L4State.observe_productive l4 (L3State.planN l2 100 s) hl4 hu

/-- **The two-axis generative ratchet.** Over any wall trajectory the L3 side
    (understanding) never regresses, and over any observation trajectory the L4
    side (meta-learning quality) never regresses. The wall pauses accrual; it never
    reverses it — on either axis. This is the global form of the per-cycle keystone
    `stable_growth_cycle`: the whole cognitive state never loses ground. -/
theorem cognitive_state_monotone
    (s : L3State) (ws : List L2State) (l4 : L4State) (l3s : List L3State) :
    s.understanding.val ≤ (L3State.run s ws).understanding.val
      ∧ l4.hypothesisQualityThreshold.val
          ≤ (L4State.observeSeq l4 l3s).hypothesisQualityThreshold.val :=
  ⟨L3State.understanding_monotone s ws, L4State.observe_monotone l4 l3s⟩

end EvoEcos
