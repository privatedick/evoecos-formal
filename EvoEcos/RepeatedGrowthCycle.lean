import EvoEcos.StableGrowthCycle

/-!
# RepeatedGrowthCycle — the ratchet across unbounded redeployment

`StableGrowthCycle.stable_growth_cycle` proves **one** danger → recovery → growth
cycle: weather a wall-up interval losing nothing, then resume and grow.
`UnderstandingRatchet.understanding_monotone` proves understanding never *decreases*
over any trajectory. Neither states what real deployment actually is: **many**
danger/recovery cycles in succession, and a *quantitative* guarantee that growth
accrues across all of them.

This file closes that gap. A deployment is a list of cycles, each a danger
interval (wall up throughout) followed by `n` safe planning steps once resumed.
The results (0 sorry, 0 axiom):

* `runCycle_active`        — a cycle preserves the `active` flag.
* `runCycle_lower`         — one cycle adds at least `min 1 (u₀ + n/100)`: the
                             danger interval contributes exactly zero, the `n`
                             safe steps contribute their full increment.
* `runCycles_lower`        — **the multi-cycle ratchet.** Over an arbitrary
                             sequence of cycles, final understanding is at least
                             `min 1 (u₀ + (total safe steps)/100)`. Growth depends
                             only on *total* safe time, however finely the danger
                             intervals chop it up. The wall pauses; it never
                             reverses, across unboundedly many cycles.
* `runCycles_reaches_max`  — **generative liveness.** If the safe steps sum to at
                             least 100 — no matter how fragmented by danger —
                             understanding reaches full `1`. The single-cycle
                             `reaches_max` becomes interruption-proof.

Design note: the bound is stated with the cap `min 1 (·)` carried through the
induction via `min_one_add_mono`, because once understanding saturates at `1` a
later cycle cannot push the *bound* past `1` either — the cap is part of the
invariant, not an afterthought.
-/

namespace EvoEcos

/-- Carrying the unit-interval cap through an additive step: if `a` already
    dominates the capped bound `min 1 c`, then after adding the same nonnegative
    `d` to both, `a`'s capped bound still dominates. This is what lets the
    per-cycle lower bound compose across the whole deployment. -/
theorem min_one_add_mono {a c d : ℝ} (h : min 1 c ≤ a) (hd : 0 ≤ d) :
    min 1 (c + d) ≤ min 1 (a + d) := by
  rcases le_total c 1 with hc | hc
  · -- below the cap: min 1 c = c ≤ a, so c + d ≤ a + d and min is monotone
    rw [min_eq_right hc] at h
    exact min_le_min (le_refl 1) (by linarith)
  · -- at the cap: min 1 c = 1 ≤ a, so both sides are already 1
    rw [min_eq_left hc] at h
    rw [min_eq_left (by linarith : (1 : ℝ) ≤ c + d),
        min_eq_left (by linarith : (1 : ℝ) ≤ a + d)]

namespace L3State

/-- One deployment cycle: weather a danger interval `c.1` (wall up throughout),
    then `resume` and take `c.2` safe planning steps against `l2safe`. -/
noncomputable def runCycle (l2safe : L2State) (s : L3State)
    (c : List L2State × Nat) : L3State :=
  planN l2safe c.2 (resume (run s c.1))

/-- Run a whole sequence of cycles, threading the state through. -/
noncomputable def runCycles (l2safe : L2State) : L3State → List (List L2State × Nat) → L3State
  | s, [] => s
  | s, c :: rest => runCycles l2safe (runCycle l2safe s c) rest

/-- Total number of safe planning steps across all cycles. -/
def totalSafe (cycles : List (List L2State × Nat)) : Nat :=
  (cycles.map Prod.snd).sum

/-- A cycle preserves `active`: the danger run, the resume, and the planning
    steps all carry the flag through. -/
theorem runCycle_active (l2safe : L2State) (s : L3State) (c : List L2State × Nat) :
    (runCycle l2safe s c).active = s.active := by
  unfold runCycle
  rw [planN_active, resume_active, run_active]

/-- **One cycle's quantitative ratchet.** Starting active, with a safe target and
    a danger interval that is wall-up throughout: the danger interval preserves
    understanding exactly, then the `c.2` resumed safe steps add their full
    capped increment. Net: at least `min 1 (u₀ + c.2/100)`. -/
theorem runCycle_lower (l2safe : L2State) (s : L3State) (c : List L2State × Nat)
    (ha : s.active = true) (hsafe : l2safe.wall = false)
    (hdanger : ∀ l2 ∈ c.1, l2.wall = true) :
    min 1 (s.understanding.val + (c.2 : ℝ) / 100)
      ≤ (runCycle l2safe s c).understanding.val := by
  unfold runCycle
  -- After the danger run and resume: understanding preserved, active, unblocked.
  have hpres : (resume (run s c.1)).understanding.val = s.understanding.val := by
    rw [resume_understanding, run_blocked_preserves c.1 s hdanger]
  have hact : (resume (run s c.1)).active = true := by
    rw [resume_active, run_active]; exact ha
  have hblk : (resume (run s c.1)).blocked = false := resume_blocked _
  have hlow := planN_lower l2safe c.2 (resume (run s c.1)) hact hblk hsafe
  rw [hpres] at hlow
  exact hlow

/-- **The multi-cycle ratchet.** Over an arbitrary sequence of danger→resume→growth
    cycles, final understanding is at least `min 1 (u₀ + (total safe steps)/100)`.
    Every danger interval contributes zero; the accrued growth depends only on the
    *total* safe time, no matter how many times danger interrupts it. -/
theorem runCycles_lower (l2safe : L2State) (hsafe : l2safe.wall = false) :
    ∀ (cycles : List (List L2State × Nat)) (s : L3State),
      s.active = true →
      (∀ c ∈ cycles, ∀ l2 ∈ c.1, l2.wall = true) →
      min 1 (s.understanding.val + (totalSafe cycles : ℝ) / 100)
        ≤ (runCycles l2safe s cycles).understanding.val
  | [], s, _, _ => by
      simp only [runCycles, totalSafe, List.map_nil, List.sum_nil, Nat.cast_zero]
      have hz : s.understanding.val + (0 : ℝ) / 100 = s.understanding.val := by ring
      rw [hz]
      exact min_le_right _ _
  | c :: rest, s, ha, hdanger => by
      simp only [runCycles]
      -- danger hypotheses for this cycle and for the tail
      have hc_danger : ∀ l2 ∈ c.1, l2.wall = true :=
        fun l2 hl => hdanger c (by simp) l2 hl
      have hrest_danger : ∀ c' ∈ rest, ∀ l2 ∈ c'.1, l2.wall = true :=
        fun c' hc' => hdanger c' (List.mem_cons_of_mem _ hc')
      -- one-cycle bound, and the active flag survives into the recursion
      have hcyc := runCycle_lower l2safe s c ha hsafe hc_danger
      have ha' : (runCycle l2safe s c).active = true := by
        rw [runCycle_active]; exact ha
      have hrec := runCycles_lower l2safe hsafe rest (runCycle l2safe s c) ha' hrest_danger
      -- compose: carry the cap through the tail's added increment
      have hstep := min_one_add_mono hcyc
        (by positivity : (0 : ℝ) ≤ (totalSafe rest : ℝ) / 100)
      -- arithmetic: total over (c :: rest) splits as this cycle + the tail
      have hcast : (totalSafe (c :: rest) : ℝ) = (c.2 : ℝ) + (totalSafe rest : ℝ) := by
        have hnat : totalSafe (c :: rest) = c.2 + totalSafe rest := by
          simp only [totalSafe, List.map_cons, List.sum_cons]
        rw [hnat]; push_cast; ring
      have heq : s.understanding.val + (totalSafe (c :: rest) : ℝ) / 100
          = (s.understanding.val + (c.2 : ℝ) / 100) + (totalSafe rest : ℝ) / 100 := by
        rw [hcast]; ring
      rw [heq]
      exact le_trans hstep hrec

/-- **Generative liveness, interruption-proof.** If the safe planning steps across
    all cycles sum to at least 100 — however finely the danger intervals fragment
    them — understanding reaches its maximum `1`. The single-cycle `reaches_max`
    survives arbitrary interruption: only the *total* safe budget matters. -/
theorem runCycles_reaches_max (l2safe : L2State) (hsafe : l2safe.wall = false)
    (cycles : List (List L2State × Nat)) (s : L3State)
    (ha : s.active = true)
    (hdanger : ∀ c ∈ cycles, ∀ l2 ∈ c.1, l2.wall = true)
    (henough : 100 ≤ totalSafe cycles) :
    (runCycles l2safe s cycles).understanding.val = 1 := by
  have hlow := runCycles_lower l2safe hsafe cycles s ha hdanger
  have hu0 : (0 : ℝ) ≤ s.understanding.val := s.understanding.property.1
  have hcap : min 1 (s.understanding.val + (totalSafe cycles : ℝ) / 100) = 1 := by
    apply min_eq_left
    have h100 : (100 : ℝ) ≤ (totalSafe cycles : ℝ) := by exact_mod_cast henough
    have : (1 : ℝ) ≤ (totalSafe cycles : ℝ) / 100 := by linarith
    linarith
  rw [hcap] at hlow
  have hle := (runCycles l2safe s cycles).understanding.property.2
  linarith

end L3State
end EvoEcos
