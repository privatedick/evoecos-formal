import EvoEcos.ACD
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Goal-Selector Chain ≥ Parallel Invasion (Structural)

**Date:** 2026-07-21

## Statement

The goal-selector ablation experiment
(`src/experiments/experiment_goal_selector_ablation.py`) compares two
dependency models for the five-condition goal-selector pipeline:

* **CHAIN** (EvoEcos L1→L4 pipeline order c→a→b→d→e): a broken stage
  also breaks every DOWNSTREAM stage (sets their reliability to r_OFF).
* **PARALLEL** (independent locks): only the broken stage uses r_OFF;
  every other stage uses r_ON.

The structural claim: under the CHAIN model, theater invasion
probability is ALWAYS at least under the PARALLEL model, for any
single-break configuration. Formally, for every break position `i`:

    1 - Π_chain(i) ≥ 1 - Π_parallel(i)

where `Π_chain(i)` and `Π_parallel(i)` are the products of stage
reliabilities under the two models. The inequality is structural — it
depends only on `r_OFF ≤ r_ON` for every stage, not on the specific
numerical values of the reliabilities.

## Why mechanize this (and not the threshold)

The arithmetic threshold `P_invade > 0.75` (DESIGN NOTE 2 of the
experiment) is a computation over fixed parameters — not a structural
fact and not worth mechanizing. The CHAIN ≥ PARALLEL inequality, by
contrast, is parameter-independent: it holds for any choice of
reliabilities with `r_OFF ≤ r_ON`. That makes it a structural theorem,
the kind of claim that belongs in the formal layer.

## What this file proves (0 sorry)

* `chainReliable_le_parallelReliable` — pointwise: the chain
  reliability at any stage is ≤ the parallel reliability.
* `chainProduct_le_parallelProduct` — product form of the above.
* `chain_invade_ge_parallel_invade` — **MAIN THEOREM**: under the chain
  model, theater invasion probability is ≥ parallel, for any
  single-break config.
* `chain_equals_parallel_at_last_stage` — boundary case: when the
  break is at the last stage (no downstream cascade), the two models
  coincide. Shows the main inequality is tight.

The proof is a single step from the pointwise inequality plus product
monotonicity for nonneg reals (helper `finset_prod_le_prod_helper`).
The arithmetic is trivial once the structural fact is established;
that is the whole point.

## Empirical companion

`src/experiments/experiment_goal_selector_ablation.py` runs both
dependency models under the same per-stage reliabilities (R_ON = 0.99,
R_OFF ∈ {0.10, 0.50, 0.05, 0.30, 0.30}). The formal result here
explains why CHAIN fixation rates are uniformly ≥ PARALLEL fixation
rates in that experiment's H4 hypothesis: the dependency structure
(not the conditions alone) is load-bearing for the conditions' joint
necessity.

## Related results

* `ThermostatSetpoint.lean` — stylistic analog: small structure + a
  few theorems formalising a structural claim from an experiment.
* `ACD.lean` — observational dichotomy (unrelated mathematically, same
  namespace conventions).
-/

namespace EvoEcos.GoalSelector

/-! ## The five-stage pipeline -/

/-- The five stages of the goal-selector pipeline in chain dependency order:
(c) constraint generation → (a) ACD(i) signal → (b) binary gate →
(d) incentive compatibility → (e) rotating certification.

Indexed by `Fin 5` with `0` = c (most upstream) through `4` = e (most
downstream). The chain order is `c < a < b < d < e`. -/
abbrev Stage := Fin 5

/-! ## Reliability parameters and hypothesis

Reliability parameters: `rOn` is the functional-stage reliability
(r_ON in the experiment), `rOff` is the broken-stage reliability
(r_OFF). The hypothesis `h_order` is the only assumption needed for
the structural theorem: every stage's broken reliability is
non-negative and at most its functional reliability. -/

variable (rOn rOff : Stage → ℝ)

/-- The ordering hypothesis: every stage's broken reliability is at
most its functional reliability, and is non-negative. This is the only
assumption on `rOn`/`rOff` for the structural theorem. -/
abbrev Order := ∀ j : Stage, 0 ≤ rOff j ∧ rOff j ≤ rOn j

/-! ## The two dependency models -/

/-- CHAIN model: stage `j` is reliable iff `j < i` (strictly upstream
of the break at `i`). Otherwise `j` is broken — the broken stage
itself AND all DOWNSTREAM stages use `rOff`. This reflects the EvoEcos
pipeline dependency: an upstream failure starves every downstream
stage of its input. -/
def chainReliable (i : Stage) (j : Stage) : ℝ :=
  if j < i then rOn j else rOff j

/-- PARALLEL model: only stage `i` (the broken one) uses `rOff`; all
others use `rOn`. Stages are treated as independent locks. -/
def parallelReliable (i : Stage) (j : Stage) : ℝ :=
  if j = i then rOff j else rOn j

/-- Probability the pipeline BLOCKS theater under CHAIN = product of
stage reliabilities (independent failures across stages). -/
def chainProduct (i : Stage) : ℝ := ∏ j : Stage, chainReliable rOn rOff i j

/-- Probability the pipeline BLOCKS theater under PARALLEL. -/
def parallelProduct (i : Stage) : ℝ := ∏ j : Stage, parallelReliable rOn rOff i j

/-- Theater invasion probability under CHAIN = 1 − blocking probability. -/
def chainInvade (i : Stage) : ℝ := 1 - chainProduct rOn rOff i

/-- Theater invasion probability under PARALLEL. -/
def parallelInvade (i : Stage) : ℝ := 1 - parallelProduct rOn rOff i

/-! ## Pointwise structural fact -/

/-- In the chain model with break at `i`, every stage's reliability is ≤
its reliability under the parallel model with the same break. This is
the load-bearing structural fact: the chain breaks at least as many
stages as parallel does, never fewer. Verified by case analysis on the
position of `j` relative to `i`:

* `j < i`: chain uses `rOn j` (upstream of break, functional);
  parallel uses `rOn j` too (only `i` is broken). Equal.
* `j = i`: chain uses `rOff i` (broken); parallel uses `rOff i`. Equal.
* `j > i`: chain uses `rOff j` (downstream of break, starved);
  parallel uses `rOn j` (independent). Chain ≤ parallel by `h_order`.
-/
theorem chainReliable_le_parallelReliable (h_order : Order rOn rOff)
    (i j : Stage) :
    chainReliable rOn rOff i j ≤ parallelReliable rOn rOff i j := by
  unfold chainReliable parallelReliable
  by_cases hj : j < i
  · -- chain uses rOn j (j is upstream of break)
    rw [if_pos hj]
    -- parallel: since j < i, j ≠ i, so also uses rOn j
    rw [if_neg (ne_of_lt hj)]
  · -- chain uses rOff j (not upstream, so broken — possibly the break
    --    itself, possibly downstream of it)
    rw [if_neg hj]
    by_cases heq : j = i
    · -- parallel: j = i, so uses rOff i — same as chain. Equality.
      rw [if_pos heq]
    · -- parallel: j ≠ i, so uses rOn j. Chain uses rOff j ≤ rOn j.
      rw [if_neg heq]
      exact (h_order j).2

/-- Every stage's chain reliability is non-negative. -/
theorem chainReliable_nonneg (h_order : Order rOn rOff) (i j : Stage) :
    0 ≤ chainReliable rOn rOff i j := by
  unfold chainReliable
  split
  · -- rOn j: from 0 ≤ rOff j ≤ rOn j, transitivity gives 0 ≤ rOn j
    exact le_trans (h_order j).1 (h_order j).2
  · -- rOff j: directly from h_order
    exact (h_order j).1

/-! ## Product monotonicity (helper) -/

/-- Helper: product of nonneg reals is nonneg. -/
private lemma finset_prod_nonneg_helper {α : Type*} [DecidableEq α]
    (s : Finset α) (f : α → ℝ) (h : ∀ a ∈ s, 0 ≤ f a) :
    0 ≤ s.prod f := by
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact mul_nonneg (h a (Finset.mem_insert_self _ _)) (ih (by aesop))

/-- Helper: product monotonicity for nonneg reals. If each `f a ≤ g a`
and each `f a ≥ 0`, then `∏ f ≤ ∏ g` over any finite set. -/
private lemma finset_prod_le_prod_helper {α : Type*} [DecidableEq α]
    (s : Finset α) (f g : α → ℝ)
    (h_nonneg_f : ∀ a ∈ s, 0 ≤ f a)
    (h_le : ∀ a ∈ s, f a ≤ g a) :
    s.prod f ≤ s.prod g := by
  induction s using Finset.induction with
  | empty => rfl
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    -- Goal: f a * s.prod f ≤ g a * s.prod g
    -- mul_le_mul arg order: h1: a ≤ c, h2: b ≤ d, h3: 0 ≤ b, h4: 0 ≤ c
    refine mul_le_mul ?_ ?_ ?_ ?_
    · -- h1: f a ≤ g a
      exact h_le a (Finset.mem_insert_self _ _)
    · -- h2: s.prod f ≤ s.prod g
      exact ih (fun x hx => h_nonneg_f x (Finset.mem_insert_of_mem hx))
               (fun x hx => h_le x (Finset.mem_insert_of_mem hx))
    · -- h3: 0 ≤ s.prod f
      apply finset_prod_nonneg_helper
      intro x hx
      exact h_nonneg_f x (Finset.mem_insert_of_mem hx)
    · -- h4: 0 ≤ g a (from 0 ≤ f a ≤ g a)
      exact le_trans (h_nonneg_f a (Finset.mem_insert_self _ _))
                     (h_le a (Finset.mem_insert_self _ _))

/-! ## Product inequality -/

/-- The product of stage reliabilities under the CHAIN model is ≤ the
product under the PARALLEL model, for any single break position. -/
theorem chainProduct_le_parallelProduct (h_order : Order rOn rOff)
    (i : Stage) :
    chainProduct rOn rOff i ≤ parallelProduct rOn rOff i := by
  unfold chainProduct parallelProduct
  refine finset_prod_le_prod_helper Finset.univ _ _ ?_ ?_
  · intro j _
    exact chainReliable_nonneg rOn rOff h_order i j
  · intro j _
    exact chainReliable_le_parallelReliable rOn rOff h_order i j

/-! ## Main theorem -/

/-- **Main theorem.** Under the CHAIN dependency model, theater invasion
probability is ALWAYS at least under the PARALLEL model, for any
single-break configuration. The inequality is purely structural — it
requires only that `r_OFF ≤ r_ON` at every stage, not any specific
numerical values.

This formalises the structural half of H4 in
`experiment_goal_selector_ablation.py`: the dependency structure
(chain vs parallel) is load-bearing for the conditions' joint
necessity. Chain fixation ≥ parallel fixation follows directly from
this probability ordering (under the experiment's Bernoulli-invasion
model, fixation is monotone in invasion probability).

The proof is one `linarith` step from `chainProduct_le_parallelProduct`:
`1 - a ≥ 1 - b` follows from `a ≤ b`. -/
theorem chain_invade_ge_parallel_invade (h_order : Order rOn rOff)
    (i : Stage) :
    chainInvade rOn rOff i ≥ parallelInvade rOn rOff i := by
  unfold chainInvade parallelInvade
  linarith [chainProduct_le_parallelProduct rOn rOff h_order i]

/-! ## Boundary case (tightness)

When the break is at the LAST stage (`i = 4`, stage `e`), the chain has
no downstream stages to cascade into. The chain and parallel products
are equal, so the invasion probabilities are equal. This shows the main
theorem's inequality is TIGHT — it cannot be strengthened to strict `>`
without additional hypotheses. -/

/-- When the break is at the last stage (no downstream cascade), the
chain and parallel models give identical invasion probabilities. -/
theorem chain_equals_parallel_at_last_stage :
    chainInvade rOn rOff 4 = parallelInvade rOn rOff 4 := by
  -- For every j, chainReliable 4 j = parallelReliable 4 j:
  --   j < 4 ⟹ chain = rOn j; parallel: j ≠ 4, so rOn j. Equal.
  --   j = 4 ⟹ chain = rOff 4 (since ¬ 4 < 4); parallel: j = 4, so rOff 4.
  -- Hence the products are equal, hence the invasions are equal.
  have key : ∀ j : Fin 5,
      chainReliable rOn rOff 4 j = parallelReliable rOn rOff 4 j := by
    intro j
    fin_cases j <;> rfl
  -- The products are equal by pointwise equality over Finset.univ.
  have hprod : chainProduct rOn rOff 4 = parallelProduct rOn rOff 4 := by
    unfold chainProduct parallelProduct
    exact Finset.prod_congr rfl (fun j _ => key j)
  -- Hence 1 - chainProduct = 1 - parallelProduct.
  unfold chainInvade parallelInvade
  rw [hprod]

end EvoEcos.GoalSelector
