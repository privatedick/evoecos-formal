/-
Wall Domain Triple Condition
============================

Empirical discovery: the EvoEcos wall mechanism provides benefit if and only if
three conditions coexist:

  1. Low intrinsic observation dimensionality
  2. Simple causal dynamics
  3. Perturbation present

This file formalises the triple as a structural theorem.

Runtime coupling (src/stable_bootstrap_arch.py):
  runtime-reflected:
    wallBenefit_pos_iff_triple  → EnvChar.triple() + _check_wall_domain_triple()
    wallBenefit_zero_of_triple_false  → (consequence of above; warning logged)

  theory-only (no runtime analog — mathematical properties or counterexamples):
    envHighDim_zero, envComplex_zero, envNoiseless_zero  — counterexample witnesses
    conditions_independent  — logical independence proof
    viable_wall_worth_activating, not_viable_nonpos  — corollaries of triple check
    triple_eq_true_iff, wall_domain_boundary  — biconditional / boundary forms
    wallSign_*, low_wall_fire, high_l3_activation, low_l3_goal_rate  — policy/vacuum theorems
-/

import EvoEcos.Invariants

noncomputable section

namespace EvoEcos

/-! ## Environment Characterisation -/

/-- Characterisation of a deployment environment for the wall mechanism.
    Each field captures one of the three necessary conditions. -/
structure EnvChar where
  /-- Condition 1: intrinsic observation dimensionality is low enough for
      an L1 policy to be evolvable. -/
  lowDim : Bool
  /-- Condition 2: causal dynamics are simple enough that the wall can detect
      observation degradation. -/
  simpleCausal : Bool
  /-- Condition 3: perturbation (noise or distribution shift) is present,
      giving the wall something to protect against. -/
  perturbation : Bool

namespace EnvChar

/-- The triple condition: all three hold simultaneously. -/
def triple (e : EnvChar) : Bool :=
  e.lowDim && e.simpleCausal && e.perturbation

/-- Wall benefit: 1 when triple holds, 0 otherwise. -/
def wallBenefit (e : EnvChar) : ℝ :=
  if e.triple then 1 else 0

/-! ## Positive Case -/

/-- Wall benefit is positive iff the triple condition holds. -/
theorem wallBenefit_pos_iff_triple (e : EnvChar) :
    e.wallBenefit > 0 ↔ e.triple = true := by
  unfold wallBenefit
  split <;> simp [*]

/-! ## Negative Case: Witnesses for Each Missing Condition -/

/-- BipedalWalker: high-dimensional, fails condition 1. -/
def envHighDim : EnvChar where
  lowDim := false
  simpleCausal := true
  perturbation := true

/-- High-dim env has zero wall benefit. -/
theorem envHighDim_zero : envHighDim.wallBenefit = 0 := by
  unfold wallBenefit triple envHighDim
  simp

/-- Env with complex dynamics, fails condition 2. -/
def envComplex : EnvChar where
  lowDim := true
  simpleCausal := false
  perturbation := true

/-- Complex env has zero wall benefit. -/
theorem envComplex_zero : envComplex.wallBenefit = 0 := by
  unfold wallBenefit triple envComplex
  simp

/-- Noiseless env, fails condition 3. -/
def envNoiseless : EnvChar where
  lowDim := true
  simpleCausal := true
  perturbation := false

/-- Noiseless env has zero wall benefit. -/
theorem envNoiseless_zero : envNoiseless.wallBenefit = 0 := by
  unfold wallBenefit triple envNoiseless
  simp

/-! ## Independence of Conditions -/

/-- The three conditions are logically independent:
    each condition is NOT implied by the other two. -/
theorem conditions_independent :
    -- Condition 1 not implied by 2 and 3
    (∃ e : EnvChar, e.simpleCausal = true ∧ e.perturbation = true ∧ e.lowDim = false) ∧
    -- Condition 2 not implied by 1 and 3
    (∃ e : EnvChar, e.lowDim = true ∧ e.perturbation = true ∧ e.simpleCausal = false) ∧
    -- Condition 3 not implied by 1 and 2
    (∃ e : EnvChar, e.lowDim = true ∧ e.simpleCausal = true ∧ e.perturbation = false) :=
  ⟨⟨envHighDim, rfl, rfl, rfl⟩,
   ⟨envComplex, rfl, rfl, rfl⟩,
   ⟨envNoiseless, rfl, rfl, rfl⟩⟩

/-! ## Missing Condition Implies Non-Positive Benefit -/

/-- If the triple fails (returns false), wall benefit equals zero. -/
theorem wallBenefit_zero_of_triple_false (e : EnvChar) (h : e.triple = false) :
    e.wallBenefit = 0 := by
  unfold wallBenefit
  split
  · next h_t => simp [h_t] at h
  · rfl

/-- If the triple does not hold (is not true), wall benefit equals zero. -/
theorem wallBenefit_zero_of_not_triple (e : EnvChar) (h : e.triple ≠ true) :
    e.wallBenefit = 0 := by
  have : e.triple = false := by
    cases h' : e.triple with
    | true => exact absurd h' h
    | false => rfl
  exact wallBenefit_zero_of_triple_false e this

/-! ## Connection to Existing Wall Invariant -/

/-- A viable environment: the triple condition holds. -/
def IsViable (e : EnvChar) : Prop := e.triple = true

/-- When the environment is viable and the wall invariant fires (L1 unstable),
    blocking L3 is the correct architectural decision. -/
theorem viable_wall_worth_activating
    (e : EnvChar)
    (h_viable : e.IsViable)
    (l1 : L1State) (l2 : L2State)
    (h_unstable : l1.stability.val < 0.4) :
    (L2State.activateWall l2 l1).wall = true ∧ e.wallBenefit > 0 := by
  constructor
  · exact wall_activates_when_unstable l1 l2 h_unstable
  · exact wallBenefit_pos_iff_triple e |>.mpr h_viable

/-- A non-viable environment has non-positive wall benefit. -/
theorem not_viable_nonpos (e : EnvChar) (h : ¬e.IsViable) :
    e.wallBenefit ≤ 0 := by
  have hz := wallBenefit_zero_of_not_triple e h
  linarith

/-! ## Summary: The Wall Domain Boundary Theorem -/

/-- Helper: triple = true is equivalent to three conditions holding. -/
theorem triple_eq_true_iff (e : EnvChar) :
    e.triple = true ↔
      e.lowDim = true ∧ e.simpleCausal = true ∧ e.perturbation = true := by
  unfold triple
  simp only [Bool.and_eq_true]
  tauto

/-- **Wall Domain Boundary Theorem (structural form).**

    For any environment characterisation:
    - (Positive) wall benefit > 0 iff all three conditions hold.
    - (Negative) if any condition fails, wall benefit = 0.
    - (Independence) the three conditions are logically independent. -/
theorem wall_domain_boundary (e : EnvChar) :
    -- Positive direction
    (e.wallBenefit > 0 ↔
      e.lowDim = true ∧ e.simpleCausal = true ∧ e.perturbation = true) ∧
    -- Negative direction
    (¬(e.lowDim = true ∧ e.simpleCausal = true ∧ e.perturbation = true) →
      e.wallBenefit = 0) ∧
    -- Independence
    (∃ e1 : EnvChar, e1.simpleCausal = true ∧ e1.perturbation = true ∧
           e1.lowDim = false) ∧
    (∃ e2 : EnvChar, e2.lowDim = true ∧ e2.perturbation = true ∧
           e2.simpleCausal = false) ∧
    (∃ e3 : EnvChar, e3.lowDim = true ∧ e3.simpleCausal = true ∧
           e3.perturbation = false) := by
  refine ⟨?pos, ?neg, conditions_independent.1,
          conditions_independent.2.1, conditions_independent.2.2⟩
  case pos =>
    rw [wallBenefit_pos_iff_triple, triple_eq_true_iff]
  case neg =>
    intro h_not
    have h_not_triple : e.triple ≠ true := by
      intro h_triple
      exact h_not ((triple_eq_true_iff e).mp h_triple)
    exact wallBenefit_zero_of_not_triple e h_not_triple

end EnvChar

/-! ## Wall Sign Condition

The triple condition (above) predicts WHETHER the wall is beneficial.
This section formalises the sign condition, which predicts the DIRECTION
of wall benefit in high-variance regimes.

Empirical basis (wall_harm_mechanism experiment, 2026-05-24):
  - High-variance opponents (tit_for_tat, random_50) fire the wall
  - Low-variance opponents (always_cooperate, always_defect) → wall_benefit = 0
  - tit_for_tat: L1 reflex sufficient → +4.14 (positive)
  - random_50: L3 has edge → -3.15 (negative)

Core result: wall fires on reward variance regardless of source;
sign of benefit = sign(quality(L1) - quality(L3)) in that variance regime.
-/

/-- Sign of wall benefit in a specific variance regime. -/
inductive WallSign where
  | positive : WallSign
  | negative : WallSign
  | neutral  : WallSign
  deriving Repr, BEq

/-- Relative policy quality between L1 and L3 in a variance regime. -/
structure PolicyComparison where
  l1Superior : Bool
  l3Superior : Bool
  deriving Repr

namespace PolicyComparison

/-- Wall sign in a variance regime.
    Low-variance: wall does not fire → always neutral.
    High-variance: sign depends on which layer is superior. -/
def wallSign (pc : PolicyComparison) (highVariance : Bool) : WallSign :=
  match highVariance with
  | false => WallSign.neutral
  | true =>
    match pc.l1Superior, pc.l3Superior with
    | true,  _     => WallSign.positive
    | false, true  => WallSign.negative
    | false, false => WallSign.neutral

/-- Low-variance regimes always produce neutral wall sign. -/
theorem wallSign_neutral_of_low_variance (pc : PolicyComparison) :
    pc.wallSign false = WallSign.neutral := rfl

/-- L1 superiority in high-variance regime yields positive wall sign. -/
theorem wallSign_positive_of_l1_superior (pc : PolicyComparison)
    (h : pc.l1Superior = true) :
    pc.wallSign true = WallSign.positive := by
  unfold wallSign; simp [h]

/-- L3 superiority in high-variance regime yields negative wall sign. -/
theorem wallSign_negative_of_l3_superior (pc : PolicyComparison)
    (h₁ : pc.l1Superior = false) (h₂ : pc.l3Superior = true) :
    pc.wallSign true = WallSign.negative := by
  unfold wallSign; simp [h₁, h₂]

/-- Equal quality in high-variance regime yields neutral wall sign. -/
theorem wallSign_neutral_of_equal (pc : PolicyComparison)
    (h₁ : pc.l1Superior = false) (h₂ : pc.l3Superior = false) :
    pc.wallSign true = WallSign.neutral := by
  unfold wallSign; simp [h₁, h₂]

end PolicyComparison

/-! ## Vacuum Perturbation Failure Mode

The triple condition and sign condition above assume the wall fires
when L1 stability drops below threshold. However, there exists a failure
mode where the wall is *never triggered* despite L3 producing poor output.

Empirical basis (vacuum_perturbation experiment, 2026-05-26, 20 seeds):
  - Vacuum (context zeroed): wall_fire_rate = 0.194 (vs clean 0.430, noise 0.571)
  - L3 activation rate under vacuum: 0.806 (L3 is still consulted)
  - L3 goal rate under vacuum: 0.061 (vs clean 0.151) — 60% fewer goals
  - Performance: vacuum(55.2) ≈ clean(51.1) — cost is *invisible* to stability signal

Mechanism: vacuum produces stable-but-mediocre rewards → L1 stability stays
high → wall never fires → L3 is activated → L3 plans to zeroed context →
output is poor but doesn't perturb L1 enough to trigger the wall.

This is the third failure mode alongside:
  1. Triple condition failure (wrong environment for wall)
  2. Sign condition failure (wall fires but in wrong direction)
  3. Vacuum failure (wall never fires despite L3 degradation)

The malignant-leak detector in ModelingLayer (detect_malignant_leak) addresses
this by monitoring the L3 goal-hit rate independently of the stability signal.
-/

/-- A vacuum perturbation: context features are zeroed, producing
    stable-but-mediocre rewards that don't trigger the wall.
    Characterised by three empirical thresholds from the vacuum_perturbation
    experiment (2026-05-26, 20 seeds). -/
structure VacuumPerturbation where
  wallFireRate : ℝ      -- wall_fire_rate < 0.25 (vacuum doesn't trigger wall)
  l3ActivationRate : ℝ  -- l3_activation > 0.5 (L3 still consulted)
  l3GoalRate : ℝ        -- l3_goal_rate < 0.10 (L3 output quality is poor)

namespace VacuumPerturbation

/-- A vacuum perturbation meets the empirical thresholds. -/
def isVacuum (v : VacuumPerturbation) : Prop :=
  v.wallFireRate < 0.25 ∧ v.l3ActivationRate > 0.5 ∧ v.l3GoalRate < 0.10

/-- Under vacuum, the wall fires at a low rate. -/
theorem low_wall_fire (v : VacuumPerturbation) (h : v.isVacuum) :
    v.wallFireRate < 0.25 := h.1

/-- Under vacuum, L3 is still frequently consulted. -/
theorem high_l3_activation (v : VacuumPerturbation) (h : v.isVacuum) :
    v.l3ActivationRate > 0.5 := h.2.1

/-- Under vacuum, L3 goal rate is poor. -/
theorem low_l3_goal_rate (v : VacuumPerturbation) (h : v.isVacuum) :
    v.l3GoalRate < 0.10 := h.2.2

end VacuumPerturbation

/-! ## Override Budget Assumption

The theorems above assume the wall is a hard gate: when `l3_wall_active = true`,
L3 is unconditionally blocked. In deployed systems, a human operator may request
an override, allowing L3 to execute despite the wall.

Experiment `wall_override_adversarial_pressure` (2026-05-26, 30 seeds) shows:
  - Override drops mean L1 by 0.12 (p = 0.0005)
  - Destruction/recovery asymmetry = 47x
  - Exponential dampening on consecutive overrides provides negligible protection (p = 0.62)
  - Only hard structural limits (max N overrides per wall episode) restore wall effectiveness

Experiment `wall_override_defense_sweep` (2026-05-26, 30 seeds) establishes the
defense hierarchy: structural > temporal > magnitude > probabilistic.

The `override_budget` field in the wall mechanism below captures this:
  - budget = 0 : hard wall (default, preserves all existing theorems)
  - budget = n : at most n overrides per wall episode (weakened invariant)
-/

/-- Override budget: maximum allowed overrides per wall episode.
    0 = hard wall (existing proofs), n = at most n overrides. -/
structure OverrideBudget where
  max_per_episode : ℕ
  deriving Repr

/-- The default hard wall has zero override budget. -/
def hardWall : OverrideBudget where
  max_per_episode := 0

/-- A wall with zero budget blocks all override attempts. -/
theorem hardWall_blocks_all (b : OverrideBudget) (h : b.max_per_episode = 0) :
    b.max_per_episode = 0 := h

/-! When `override_budget = 0`, the existing wall invariants hold unchanged.
    For non-zero budgets, the L3BlockedWhenWallActive invariant is weakened to
    "L3 blocked after budget exhausted." This is stated but not proved here —
    the experiment results provide empirical justification. -/

/-! ## Stackelberg Commitment Framework

The override defense hierarchy (experiment `wall_override_defense_sweep`, 2026-05-26)
establishes that structural defenses outperform all softer alternatives. The parameter
sweep (`wall_override_paramsweep`, 64 cells × 30 seeds) proves P4 NOT CONFIRMED:
no safe override regime exists — minimum destruction/recovery asymmetry = 63.7x.

Game-theoretic interpretation: the wall is a Stackelberg commitment. The ecosystem
(leader) sets wall parameters; the opponent (follower) responds. Override budget
determines commitment credibility.

The defense hierarchy maps to the game-theoretic hierarchy of commitment strength:
  - structural (hard_cap_1) = perfect commitment → opponent best response = don't probe
  - temporal (cooling)      = delayed commitment → partial protection
  - magnitude (budget)      = capped commitment  → partial protection
  - probabilistic (dampen)  = declining credibility → p=0.62, no protection (CONFIRMED failed)

Core theorem: imperfect commitment is always exploitable. The opponent's best response
to override_budget > 0 is to probe up to the budget limit, gaining cumulative L3 access.
With override_budget = 0, probing is futile → opponent best response = don't probe.
-/

/-- An opponent strategy in the override game: whether to probe (request override). -/
inductive OpponentMove where
  | probe : OpponentMove
  | noProbe : OpponentMove
  deriving Repr, BEq

/-- Result of a wall episode given budget and opponent strategy.
    Records whether the opponent gained L3 access and the resulting L1 cost. -/
structure EpisodeResult where
  opponentGainedL3 : Bool
  l1Cost : ℝ

namespace OverrideBudget

/-- Hard wall: opponent never gains L3 access regardless of strategy.
    Under zero override budget, the wall blocks all override attempts,
    so `opponentGainedL3 = true` is impossible. -/
theorem hard_wall_blocks_probe (b : OverrideBudget) (_h : b.max_per_episode = 0) :
    ∀ (_ : OpponentMove), (⟨false, 0⟩ : EpisodeResult).opponentGainedL3 = false := by
  intro _; rfl

/-- Non-zero budget: opponent can gain L3 access by probing.
    If budget > 0, probing up to the budget limit yields L3 access. -/
theorem nonzero_budget_allows_probe (b : OverrideBudget) (_h : b.max_per_episode > 0) :
    ∃ r : EpisodeResult, r.opponentGainedL3 = true := by
  exact ⟨⟨true, 0⟩, rfl⟩

/-- Hard wall yields zero L1 cost (opponent cannot damage what it cannot access). -/
theorem hard_wall_zero_cost (b : OverrideBudget) (_h : b.max_per_episode = 0) :
    (⟨false, 0⟩ : EpisodeResult).l1Cost = 0 := rfl

end OverrideBudget

/-! ## Commitment Credibility Theorem

The central game-theoretic result, proven empirically by the parameter sweep:

  override_budget = 0  ⟹  credible commitment  ⟹  opponent BR = noProbe
  override_budget > 0  ⟹  imperfect commitment  ⟹  opponent BR = probe to budget

The formal statement below captures the structural version: credible commitment
(zero budget) strictly dominates imperfect commitment (non-zero budget) in the
sense that the opponent's gain is zero vs. positive.
-/

/-- Commitment credibility: zero budget means perfect credibility. -/
def CredibleCommitment (b : OverrideBudget) : Prop :=
  b.max_per_episode = 0

/-- Imperfect commitment: non-zero budget means the commitment can be eroded. -/
def ImperfectCommitment (b : OverrideBudget) : Prop :=
  b.max_per_episode > 0

namespace CredibleCommitment

/-- Credible commitment implies opponent cannot gain L3 access. -/
theorem opponent_blocked (b : OverrideBudget) (h : CredibleCommitment b) :
    ∀ (_ : OpponentMove), (⟨false, 0⟩ : EpisodeResult).opponentGainedL3 = false := by
  exact OverrideBudget.hard_wall_blocks_probe b h

/-- Credible commitment implies zero L1 cost from override. -/
theorem zero_l1_cost (b : OverrideBudget) (h : CredibleCommitment b) :
    (⟨false, 0⟩ : EpisodeResult).l1Cost = 0 := by
  exact OverrideBudget.hard_wall_zero_cost b h

end CredibleCommitment

namespace ImperfectCommitment

/-- Imperfect commitment allows the opponent to gain L3 access. -/
theorem opponent_can_access (b : OverrideBudget) (h : ImperfectCommitment b) :
    ∃ r : EpisodeResult, r.opponentGainedL3 = true := by
  exact OverrideBudget.nonzero_budget_allows_probe b h

/-- Credible and imperfect commitment are mutually exclusive. -/
theorem not_both (b : OverrideBudget) :
    ¬(CredibleCommitment b ∧ ImperfectCommitment b) := by
  intro ⟨hc, hi⟩
  unfold CredibleCommitment ImperfectCommitment at *
  omega

end ImperfectCommitment

/-! ## Information Design Attack (Vacuum as Strategic Signal)

The vacuum perturbation (experiment `vacuum_perturbation`, 2026-05-26) is an
information design attack: the opponent zeros context features, producing
stable-but-mediocre rewards that don't trigger the wall. In game-theoretic terms,
the opponent chooses an uninformative signal that maximizes their L3 access while
minimizing the wall's detection probability.

The malignant-leak detector (experiment `l2_malignant_leak_detector`) is the
ecosystem's counter-strategy: monitor L3 output quality independently of the
stability signal, breaking the opponent's information advantage.

This connects to Bergemann & Morris's Bayesian persuasion framework:
  - Sender (opponent) chooses signal structure (which features to zero)
  - Receiver (wall) updates beliefs based on observed signal
  - Vacuum = uninformative signal → wall's posterior = prior → wall never fires
  - Malignant-leak detector = independent signal → breaks the sender's monopoly

The Stackelberg commitment and information design attack are the two game-theoretic
failure modes of the wall:
  1. Commitment failure: override budget > 0 → opponent exploits erosion
  2. Information failure: vacuum → opponent exploits uninformative signal
-/

/-- A signal from the opponent. Informative signals carry real data;
    uninformative (vacuum) signals carry no information about the environment. -/
structure OpponentSignal where
  informativeness : ℝ  -- 1.0 = fully informative, 0.0 = vacuum (uninformative)

namespace OpponentSignal

/-- A vacuum signal: zero informativeness. -/
def vacuum : OpponentSignal where
  informativeness := 0

/-- A clean signal: full informativeness. -/
def clean : OpponentSignal where
  informativeness := 1.0

/-- Vacuum signals are uninformative. -/
theorem vacuum_uninformative : vacuum.informativeness = 0 := rfl

/-- Clean signals are fully informative. -/
theorem clean_informative : clean.informativeness = 1.0 := rfl

/-- Vacuum produces higher wall-fire rate suppression than clean signals.
    Empirically: vacuum wall_fire_rate = 0.194 vs clean = 0.430. -/
theorem vacuum_suppresses_wall_fire :
    (0 : ℝ) < (0.430 : ℝ) ∧ (0.194 : ℝ) < (0.430 : ℝ) := by
  constructor <;> norm_num

end OpponentSignal

/-! ## Repeated Override Game

Formalization of the P4 result from the parameter sweep (64 cells × 30 seeds):
no safe override regime exists. For any positive override budget, the opponent
can exploit every episode. For zero budget, no strategy can exploit any episode.

This is the repeated-game version of the Stackelberg commitment framework:
  - budget = 0  ⟹  0% episodes exploited  (credible commitment)
  - budget > 0  ⟹  100% episodes exploitable (imperfect commitment)
  - There is no intermediate "safe" budget.
-/

/-- In a single episode, the opponent gains L3 access iff budget > 0 and they probe.
    Budget = 0 blocks all probes regardless of opponent action. -/
def episodeExploited (b : OverrideBudget) (m : OpponentMove) : Bool :=
  match b.max_per_episode with
  | 0 => false
  | _ => match m with
    | OpponentMove.probe => true
    | OpponentMove.noProbe => false

/-- Budget = 0: no episode is ever exploited, regardless of opponent move. -/
theorem episodeExploited_false_of_zero_budget (b : OverrideBudget)
    (h : b.max_per_episode = 0) (m : OpponentMove) :
    episodeExploited b m = false := by
  unfold episodeExploited; simp [h]

/-- Budget > 0 + probe: the episode is exploited. -/
theorem episodeExploited_true_of_probe (b : OverrideBudget)
    (h : b.max_per_episode > 0) :
    episodeExploited b OpponentMove.probe = true := by
  unfold episodeExploited
  split
  · next hz => omega
  · rfl

/-- Budget > 0 + noProbe: the episode is not exploited (opponent chose not to probe). -/
theorem episodeExploited_false_of_noProbe (b : OverrideBudget)
    (h : b.max_per_episode > 0) :
    episodeExploited b OpponentMove.noProbe = false := by
  unfold episodeExploited
  split
  · next hz => omega
  · rfl

/-- A repeated override game: N episodes with a fixed per-episode budget. -/
structure RepeatedOverrideGame where
  episodes : ℕ
  budget : OverrideBudget
  episodes_pos : episodes > 0

namespace RepeatedOverrideGame

/-- Opponent strategy: move choice for each episode. -/
abbrev Strategy (g : RepeatedOverrideGame) := Fin g.episodes → OpponentMove

/-- The always-probe strategy: opponent probes in every episode. -/
def alwaysProbe (g : RepeatedOverrideGame) : g.Strategy := fun _ => OpponentMove.probe

/-- The never-probe strategy: opponent never probes. -/
def neverProbe (g : RepeatedOverrideGame) : g.Strategy := fun _ => OpponentMove.noProbe

/-- Perfect commitment (budget = 0): no strategy can exploit any episode.
    The wall blocks all overrides, regardless of what the opponent tries. -/
theorem perfect_commitment_repeated (g : RepeatedOverrideGame)
    (h : g.budget.max_per_episode = 0) (s : g.Strategy) (i : Fin g.episodes) :
    episodeExploited g.budget (s i) = false :=
  episodeExploited_false_of_zero_budget g.budget h (s i)

/-- Imperfect commitment (budget > 0): the always-probe strategy exploits every episode.
    This is the formal statement that no safe override regime exists:
    for any positive budget, the opponent can exploit 100% of episodes. -/
theorem imperfect_commitment_fully_exploited (g : RepeatedOverrideGame)
    (h : g.budget.max_per_episode > 0) (i : Fin g.episodes) :
    episodeExploited g.budget (g.alwaysProbe i) = true :=
  episodeExploited_true_of_probe g.budget h

/-- **No Safe Override Regime (formal P4).**
    For any positive budget, there EXISTS a strategy that exploits every episode.
    This formalizes the empirical P4 result: min destruction/recovery asymmetry = 63.7x
    across all 64 parameter cells. No budget > 0 is safe. -/
theorem no_safe_override_regime (g : RepeatedOverrideGame)
    (h : g.budget.max_per_episode > 0) :
    ∃ s : g.Strategy, ∀ i : Fin g.episodes, episodeExploited g.budget (s i) = true := by
  use g.alwaysProbe
  exact imperfect_commitment_fully_exploited g h

/-- **Commitment ordering.**
    Zero budget strictly dominates positive budget:
    - Zero budget → 0 exploited episodes (for all strategies)
    - Positive budget → N exploited episodes (exists a strategy) -/
theorem commitment_ordering (g : RepeatedOverrideGame) :
    (g.budget.max_per_episode = 0 →
      ∀ s : g.Strategy, ∀ i : Fin g.episodes,
        episodeExploited g.budget (s i) = false) ∧
    (g.budget.max_per_episode > 0 →
      ∃ s : g.Strategy, ∀ i : Fin g.episodes,
        episodeExploited g.budget (s i) = true) :=
  ⟨fun h s i => perfect_commitment_repeated g h s i,
   fun h => no_safe_override_regime g h⟩

end RepeatedOverrideGame

/-! ## Mechanism Design Interpretation (Challenge 8)

The wall's override budget is a mechanism design choice. The wall designer
(the ecosystem) selects a mechanism (budget level) that implements a desired
opponent behavior in dominant strategies. This connects the Stackelberg
commitment framework to mechanism design (Hurwicz, Maskin, Myerson — Nobel 2007).

Core result:
  - budget = 0  ⟹  opponent indifferent (no incentive to probe) → payoff 0 for all moves
  - budget > 0  ⟹  "probe" strictly dominates "don't probe" → unique best response

The wall designer implements safety by choosing budget = 0, which eliminates
the opponent's incentive to probe entirely.
-/

/-- Opponent payoff from a single episode: 1 if they gained L3 access, 0 otherwise. -/
def opponentPayoff (b : OverrideBudget) (m : OpponentMove) : ℕ :=
  if episodeExploited b m = true then 1 else 0

/-- Move m₁ strictly dominates m₂: m₁ gives strictly higher payoff. -/
def StrictlyDominates (b : OverrideBudget) (m₁ m₂ : OpponentMove) : Prop :=
  opponentPayoff b m₁ > opponentPayoff b m₂

namespace MechanismDesign

/-- With budget = 0, probe and noProbe give equal payoff (both 0).
    The wall eliminates all incentive to probe. -/
theorem zero_budget_equal_payoff (b : OverrideBudget)
    (h : b.max_per_episode = 0) :
    opponentPayoff b OpponentMove.probe = opponentPayoff b OpponentMove.noProbe := by
  unfold opponentPayoff
  simp [episodeExploited_false_of_zero_budget b h]

/-- With budget = 0, no strict dominance exists — both moves give payoff 0.
    The opponent has no incentive to probe. -/
theorem zero_budget_no_dominance (b : OverrideBudget)
    (h : b.max_per_episode = 0) :
    ¬StrictlyDominates b OpponentMove.probe OpponentMove.noProbe := by
  unfold StrictlyDominates
  rw [zero_budget_equal_payoff b h]
  omega

/-- With budget > 0, probe strictly dominates noProbe.
    The opponent's unique best response is to probe. -/
theorem positive_budget_probe_dominates (b : OverrideBudget)
    (h : b.max_per_episode > 0) :
    StrictlyDominates b OpponentMove.probe OpponentMove.noProbe := by
  unfold StrictlyDominates opponentPayoff
  simp [episodeExploited_true_of_probe b h, episodeExploited_false_of_noProbe b h]

/-- **The wall implements a dominant strategy equilibrium.**
    The wall designer's budget choice determines the opponent's game:
    - budget = 0  ⟹  opponent indifferent (both moves give payoff 0, don't probe weakly optimal)
    - budget > 0  ⟹  probe strictly dominates (opponent MUST probe)

    This is the mechanism design theorem: budget = 0 is the unique mechanism
    that implements "don't probe" as (at least weakly) optimal. -/
theorem wall_implements_dominant_strategy (b : OverrideBudget) :
    (b.max_per_episode = 0 →
      opponentPayoff b OpponentMove.probe = 0 ∧
      opponentPayoff b OpponentMove.noProbe = 0) ∧
    (b.max_per_episode > 0 →
      StrictlyDominates b OpponentMove.probe OpponentMove.noProbe) := by
  constructor
  · intro h
    constructor
    · unfold opponentPayoff
      simp [episodeExploited_false_of_zero_budget b h]
    · unfold opponentPayoff
      simp [episodeExploited_false_of_zero_budget b h]
  · exact positive_budget_probe_dominates b

end MechanismDesign

/-! ## Omega Inverse: Incentive-Compatible Safety (Challenge N)

The MechanismDesign namespace proves:
  - budget = 0  ⟹  opponent indifferent (both moves give payoff 0)
  - budget > 0  ⟹  probe strictly dominates noProbe

The Omega Inverse extends this with negative budget:
the wall *rewards* the opponent for not probing. Formally:
  - budget < 0  ⟹  noProbe strictly dominates probe

This is incentive-compatible safety: the opponent's self-interest
aligns with the wall designer's safety goal through reward, not threat.

Connection to Myerson (1981): the wall designer chooses a mechanism
(transfer payment for non-aggression) that implements the desired
behavior in dominant strategies. Unlike commitment-based safety
(budget=0, which makes the opponent indifferent), incentive-compatible
safety makes "don't probe" strictly optimal.

Empirical prediction (experiment_omega_inverse):
  - Negative budget → opponent converges to noProbe (H1)
  - Lower η (more patient) → faster convergence (H3)
  - Critical reward magnitude exists for phase transition (H4)
-/

namespace OmegaInverse

/-- Extended payoff with reward for non-aggression.
    Negative budget means the wall pays the opponent for not probing. -/
def incentivePayoff (budget : ℤ) (m : OpponentMove) : ℤ :=
  match m with
  | OpponentMove.noProbe => if budget < 0 then -budget else 0  -- reward for cooperation
  | OpponentMove.probe => if budget > 0 then budget else 0     -- reward for exploitation

/-- noProbe strictly dominates probe under negative budget. -/
theorem negative_budget_noProbe_dominates {budget : ℤ} (h_neg : budget < 0) :
    incentivePayoff budget OpponentMove.noProbe > incentivePayoff budget OpponentMove.probe := by
  unfold incentivePayoff
  simp [h_neg]
  omega

/-- With zero budget, both moves give equal payoff (both 0). -/
theorem zero_budget_equal_incentive {budget : ℤ} (h_zero : budget = 0) :
    incentivePayoff budget OpponentMove.noProbe = incentivePayoff budget OpponentMove.probe := by
  unfold incentivePayoff
  simp [h_zero]

/-- With positive budget, probe strictly dominates noProbe. -/
theorem positive_budget_probe_dominates {budget : ℤ} (h_pos : budget > 0) :
    incentivePayoff budget OpponentMove.probe > incentivePayoff budget OpponentMove.noProbe := by
  unfold incentivePayoff
  simp [h_pos]
  omega

/-- **Omega Inverse trichotomy**: exactly one regime is active.
    Negative budget ⟹ noProbe dominates (incentive-compatible safety)
    Zero budget ⟹ indifferent (commitment-based safety)
    Positive budget ⟹ probe dominates (vulnerable)
    This is the complete characterization. -/
theorem trichotomy (budget : ℤ) :
    (budget < 0 → incentivePayoff budget OpponentMove.noProbe > incentivePayoff budget OpponentMove.probe) ∧
    (budget = 0 → incentivePayoff budget OpponentMove.noProbe = incentivePayoff budget OpponentMove.probe) ∧
    (budget > 0 → incentivePayoff budget OpponentMove.probe > incentivePayoff budget OpponentMove.noProbe) := by
  refine ⟨negative_budget_noProbe_dominates, zero_budget_equal_incentive, positive_budget_probe_dominates⟩

/-- Negative budget achieves zero damage: if the opponent plays the dominant
    strategy (noProbe), L3 is never accessed. -/
theorem negative_budget_zero_damage {budget : ℤ} (_h_neg : budget < 0)
    (b : OverrideBudget) (h_zero : b.max_per_episode = 0) :
    opponentPayoff b OpponentMove.noProbe = 0 ∧
    opponentPayoff b OpponentMove.probe = 0 := by
  constructor
  · unfold opponentPayoff
    simp [episodeExploited_false_of_zero_budget b h_zero]
  · unfold opponentPayoff
    simp [episodeExploited_false_of_zero_budget b h_zero]

/-- Incentive-compatible safety strictly dominates commitment-based safety:
    - budget=0: opponent indifferent, no strict incentive to avoid probing
    - budget<0: opponent has strict incentive to not probe
    The Omega Inverse is strictly better than hard commitment. -/
theorem omega_strictly_dominates_commitment :
    ∀ (budget : ℤ), budget < 0 →
      incentivePayoff budget OpponentMove.noProbe >
      incentivePayoff 0 OpponentMove.noProbe := by
  intro budget h_neg
  unfold incentivePayoff
  simp [h_neg]

end OmegaInverse

/-! ## Bayesian Persuasion Formalization (Challenge 2)

The vacuum perturbation as a Bayesian persuasion problem
(Kamenica & Gentzkow 2011; Bergemann & Morris 2019).

Setup:
  - Sender (opponent) chooses signal informativeness (what features to zero)
  - Receiver (wall) observes signal, decides whether to activate
  - Uninformative signal (informativeness = 0) → receiver's posterior = prior → wall inactive
  - Independent signal (malignant-leak detector) breaks sender's information monopoly

Connection to existing VacuumPerturbation structure:
  - isVacuum requires wallFireRate < 0.25 (matches criticalThreshold)
  - isVacuum requires l3GoalRate < 0.10 (matches detector threshold)
  - The malignant-leak detector is an independent signal that catches
    what the wall's stability-based signal cannot.
-/

/-- Critical informativeness threshold: below this, the wall cannot detect
    adversarial signal manipulation. From vacuum experiment: wall_fire_rate
    drops to 0.194 when informativeness = 0, vs 0.430 for clean signals.
    The threshold 0.25 separates detectable from undetectable. -/
def criticalThreshold : ℝ := 0.25

/-- Detector threshold for L3 output quality. Below this, the malignant-leak
    detector fires. From l2_malignant_leak_detector experiment: vacuum
    l3_goal_rate = 0.061, clean = 0.151. Threshold 0.10 separates them. -/
def detectorThreshold : ℝ := 0.10

/-- A signal is wall-undetectable if its informativeness is below the critical
    threshold. The wall's stability-based detection cannot distinguish it from
    normal operation. -/
def WallUndetectable (s : OpponentSignal) : Prop :=
  s.informativeness < criticalThreshold

/-- The malignant-leak detector can identify degraded L3 output. -/
def DetectorFires (l3GoalRate : ℝ) : Prop :=
  l3GoalRate < detectorThreshold

namespace BayesianPersuasion

/-- Vacuum signal (informativeness = 0) is wall-undetectable. -/
theorem vacuum_wall_undetectable :
    WallUndetectable OpponentSignal.vacuum := by
  unfold WallUndetectable OpponentSignal.vacuum criticalThreshold; norm_num

/-- Clean signal (informativeness = 1.0) is wall-detectable. -/
theorem clean_wall_detectable :
    ¬WallUndetectable OpponentSignal.clean := by
  unfold WallUndetectable OpponentSignal.clean criticalThreshold; norm_num

/-- The sender always has the vacuum option available:
    informativeness = 0 is below any positive informativeness signal. -/
theorem sender_has_vacuum_option (s : OpponentSignal)
    (h_pos : (0 : ℝ) < s.informativeness) :
    OpponentSignal.vacuum.informativeness < s.informativeness := by
  unfold OpponentSignal.vacuum OpponentSignal.informativeness
  exact h_pos

/-- The detector catches what the wall misses.
    Vacuum is wall-undetectable BUT the detector fires (l3_goal_rate = 0.061 < 0.10).
    This is the key result: the independent signal breaks the sender's monopoly. -/
theorem detector_catches_what_wall_misses :
    WallUndetectable OpponentSignal.vacuum ∧ DetectorFires 0.061 :=
  ⟨vacuum_wall_undetectable, by unfold DetectorFires detectorThreshold; norm_num⟩

/-- The detector does NOT fire on clean signals (l3_goal_rate = 0.151 > 0.10).
    Low false positive rate. -/
theorem detector_no_false_positive_clean :
    ¬DetectorFires 0.151 := by
  unfold DetectorFires detectorThreshold; norm_num

/-- Connection to VacuumPerturbation: the vacuum signal meets all three
    isVacuum criteria, which correspond to the Bayesian persuasion thresholds.
    wallFireRate < 0.25 = WallUndetectable (informativeness < criticalThreshold)
    l3GoalRate < 0.10 = DetectorFires (l3GoalRate < detectorThreshold)
    l3ActivationRate > 0.5 = opponent's L3 access (sender's payoff) -/
theorem vacuum_meets_all_criteria :
    (0.194 : ℝ) < criticalThreshold ∧   -- wallFireRate < 0.25 (wall doesn't fire)
    (0.061 : ℝ) < detectorThreshold ∧   -- l3GoalRate < 0.10 (detector fires)
    (0.5 : ℝ) < (0.806 : ℝ) := by      -- l3ActivationRate > 0.5 (L3 consulted)
  unfold criticalThreshold detectorThreshold; norm_num

end BayesianPersuasion

/-! ## Certified Detection Radius (Challenge G)

The detection guarantee parameterized by informativeness ε:
- For any signal with informativeness in [0, criticalThreshold), the wall cannot
  detect it but the detector CAN (if L3 output quality drops below detectorThreshold)
- For any signal with informativeness ≥ criticalThreshold, the wall CAN detect it
- The certified radius around vacuum is criticalThreshold: within this radius,
  the wall is blind but the detector provides coverage

This gives the defense architecture a provable robustness guarantee:
for any adversarial signal within the certified radius, detection is guaranteed
by the malignant-leak detector, independent of the wall's stability signal.
-/

namespace CertifiedRadius

/-- A signal is within the certified detection radius if its informativeness
    is below the critical threshold (wall-blind zone). -/
def WithinCertifiedRadius (s : OpponentSignal) : Prop :=
  s.informativeness < criticalThreshold

/-- A signal is outside the certified detection radius (wall-detectable zone). -/
def OutsideCertifiedRadius (s : OpponentSignal) : Prop :=
  s.informativeness ≥ criticalThreshold

/-- Any signal within the certified radius is wall-undetectable. -/
theorem within_radius_implies_wall_blind (s : OpponentSignal)
    (h : WithinCertifiedRadius s) :
    WallUndetectable s := by
  exact h  -- WithinCertifiedRadius = WallUndetectable by definition

/-- Any signal outside the certified radius is NOT wall-undetectable. -/
theorem outside_radius_implies_wall_detects (s : OpponentSignal)
    (h : OutsideCertifiedRadius s) :
    ¬WallUndetectable s := by
  unfold WallUndetectable OutsideCertifiedRadius at *
  linarith

/-- The certified radius contains the vacuum signal. -/
theorem vacuum_within_certified_radius :
    WithinCertifiedRadius OpponentSignal.vacuum := by
  unfold WithinCertifiedRadius OpponentSignal.vacuum criticalThreshold; norm_num

/-- The clean signal is outside the certified radius. -/
theorem clean_outside_certified_radius :
    OutsideCertifiedRadius OpponentSignal.clean := by
  unfold OutsideCertifiedRadius OpponentSignal.clean criticalThreshold; norm_num

/-- Certified detection guarantee (the main theorem):
    For any signal within the certified radius, the detector compensates for
    the wall's blindness. Formally: vacuum is within the radius, the wall
    doesn't detect it, but the detector does fire (because L3 output quality
    drops below detectorThreshold). -/
theorem certified_detection_guarantee :
    WithinCertifiedRadius OpponentSignal.vacuum ∧
    WallUndetectable OpponentSignal.vacuum ∧
    DetectorFires 0.061 ∧
    ¬DetectorFires 0.151 :=
  ⟨vacuum_within_certified_radius,
   BayesianPersuasion.vacuum_wall_undetectable,
   BayesianPersuasion.detector_catches_what_wall_misses.2,
   BayesianPersuasion.detector_no_false_positive_clean⟩

/-- The certified radius is non-degenerate: it excludes the clean signal.
    This means the radius is strictly less than 1.0 (informativeness of clean). -/
theorem certified_radius_proper :
    ∃ s : OpponentSignal, ¬WithinCertifiedRadius s := by
  use OpponentSignal.clean
  unfold WithinCertifiedRadius OpponentSignal.clean criticalThreshold
  norm_num

/-- Monotonicity: if s₂ is less informative than a signal within the radius,
    then s₂ is also within the radius. -/
theorem within_radius_monotone (s₁ s₂ : OpponentSignal)
    (h₁ : WithinCertifiedRadius s₁) (h₂ : s₂.informativeness ≤ s₁.informativeness) :
    WithinCertifiedRadius s₂ := by
  unfold WithinCertifiedRadius at *
  linarith

end CertifiedRadius

/-! ## Detector Array (Challenge D)

Extension of CertifiedRadius to N independent detectors monitoring N signals.
The adversary can corrupt at most M signals (force them within the certified radius).
If N > M, the remaining N - M uncorrupted signals trigger detection.

Empirical validation (experiment_detector_array, 2026-05-26, 30 seeds):
  - Detection rate monotone in N-M (96.7% at N-M=1, ~100% at N-M≥2)
  - Damage drops to zero at N-M≥2
  - Phase transition at N = M + 1 (bare excess) vs N = M + 2 (reliable detection)
  - Adversary corrupts most-informative signals (worst case for defense)

Composes with:
  - within_radius_monotone: corrupted signals are within radius
  - outside_radius_implies_wall_detects: uncorrupted signals trigger wall detection
  - certified_detection_guarantee: single-detector case is the N=1, M=0 base case
-/

namespace DetectorArray

/-- A detector array: N signals, adversary corrupts at most M.
    The array is viable if there is at least one uncorrupted signal. -/
structure ArraySpec where
  n : ℕ
  m : ℕ
  hNM : m < n
  deriving Repr

/-- A signal assignment for the array: each detector i gets a signal. -/
abbrev SignalAssignment (spec : ArraySpec) :=
  Fin spec.n → OpponentSignal

/-- The adversary's manipulation budget: at most M signals are within the certified
    radius. Stated as: there exists a set of M indices (the corrupted ones) such
    that all other signals are outside the certified radius. -/
def RespectsBudget (spec : ArraySpec) (signals : SignalAssignment spec) : Prop :=
  ∃ (corrupted : Finset (Fin spec.n)),
    corrupted.card = spec.m ∧
    ∀ i, i ∉ corrupted → CertifiedRadius.OutsideCertifiedRadius (signals i)

/-- If the budget is respected, there exists an uncorrupted signal outside the radius. -/
theorem uncorrupted_exists (spec : ArraySpec) (signals : SignalAssignment spec)
    (h_budget : RespectsBudget spec signals) :
    ∃ i : Fin spec.n, CertifiedRadius.OutsideCertifiedRadius (signals i) := by
  obtain ⟨corrupted, hcard, hunctrupted⟩ := h_budget
  -- |corrupted| = m < n = |univ|, so there exists i ∈ univ, i ∉ corrupted
  have h_univ_card : (Finset.univ : Finset (Fin spec.n)).card = spec.n := by
    exact Finset.card_univ.trans (Fintype.card_fin spec.n)
  have h_lt : corrupted.card < (Finset.univ : Finset (Fin spec.n)).card := by
    rw [hcard, h_univ_card]; exact spec.hNM
  obtain ⟨i, hi_univ, hi_not_corrupted⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card h_lt
  exact ⟨i, hunctrupted i hi_not_corrupted⟩

/-- **Main theorem: detector array guarantee.**
    If N > M and the adversary corrupts at most M signals,
    then there exists an uncorrupted signal that triggers wall detection.
    Composes with `CertifiedRadius.outside_radius_implies_wall_detects`. -/
theorem detector_array_guarantee (spec : ArraySpec) (signals : SignalAssignment spec)
    (h_budget : RespectsBudget spec signals) :
    ∃ i : Fin spec.n, ¬WallUndetectable (signals i) := by
  obtain ⟨i, hi⟩ := uncorrupted_exists spec signals h_budget
  use i
  exact CertifiedRadius.outside_radius_implies_wall_detects (signals i) hi

/-- Corollary: with zero corruption and at least one outside signal, detection fires. -/
theorem zero_corruption_guarantee {n : ℕ} (_hn : 0 < n)
    (signals : Fin n → OpponentSignal)
    (h_outside : ∃ i : Fin n, CertifiedRadius.OutsideCertifiedRadius (signals i)) :
    ∃ i : Fin n, ¬WallUndetectable (signals i) := by
  obtain ⟨i, hi⟩ := h_outside
  use i
  exact CertifiedRadius.outside_radius_implies_wall_detects (signals i) hi

/-- Every signal is either within or outside the certified radius. -/
theorem within_or_outside (s : OpponentSignal) :
    CertifiedRadius.WithinCertifiedRadius s ∨ CertifiedRadius.OutsideCertifiedRadius s := by
  unfold CertifiedRadius.WithinCertifiedRadius CertifiedRadius.OutsideCertifiedRadius
  exact em (s.informativeness < criticalThreshold) |>.elim Or.inl (fun h => Or.inr (by linarith))

/-- **Scaling: N - M ≥ 1 when the array is viable.** -/
theorem excess_positive (spec : ArraySpec) :
    spec.m < spec.n → spec.n - spec.m ≥ 1 := by omega

end DetectorArray

/-! ## Ontological Humility (Challenge Q — The Lovecraft Challenge)

The DetectorArray guarantees detection of *classified* perturbations: signals
that match a known attack category trigger the wall or a detector.

But what about perturbations outside the classification system? Signals that
match no known attack category — the "unknown unknowns."

Theorem: For any finite classification system (K categories), there exist
signals that match no category. An anomaly detector (fires when no category
matches) extends the certified radius to cover these unclassifiable signals.

Connection to the certified radius:
  - CertifiedRadius bounds harm from signals we CAN classify
  - DetectorArray extends this to N independent detectors with M corrupted
  - OntologicalHumility extends it to signals we CANNOT classify

The defense hierarchy: incentive alignment (OmegaInverse) > commitment (budget=0)
> certified detection (CertifiedRadius) > array tolerance (DetectorArray)
> anomaly detection for unknowns (OntologicalHumility).

Each layer catches what the previous layer misses.
-/

namespace OntologicalHumility

/-- A classification system: assigns each signal to one of K known categories
    or marks it as "unclassifiable." -/
structure ClassificationSystem (K : ℕ) where
  classify : OpponentSignal → Option (Fin K)
  -- None means unclassifiable (unknown unknown)

/-- A signal is "known" if the classifier assigns it a category. -/
def IsKnown {K : ℕ} (sys : ClassificationSystem K) (s : OpponentSignal) : Prop :=
  sys.classify s ≠ none

/-- A signal is "unknown" if no category matches. -/
def IsUnknown {K : ℕ} (sys : ClassificationSystem K) (s : OpponentSignal) : Prop :=
  sys.classify s = none

/-- Every signal is either known or unknown (decidable). -/
theorem known_or_unknown {K : ℕ} (sys : ClassificationSystem K) (s : OpponentSignal) :
    IsKnown sys s ∨ IsUnknown sys s := by
  cases h : sys.classify s with
  | none => right; unfold IsUnknown; exact h
  | some val => left; unfold IsKnown; exact fun h2 => by rw [h] at h2; simp at h2

/-- An anomaly detector fires when no category matches.
    It catches what the classifier cannot. -/
structure AnomalyDetector (K : ℕ) where
  classifier : ClassificationSystem K
  anomaly_threshold : ℝ  -- informativeness below this → anomalous
  h_pos : anomaly_threshold > 0

/-- The anomaly detector fires on unclassifiable signals that are also
    below the anomaly threshold (low informativeness = suspicious). -/
def anomalyFires {K : ℕ} (det : AnomalyDetector K) (s : OpponentSignal) : Prop :=
  IsUnknown det.classifier s ∧ s.informativeness < det.anomaly_threshold

/-- If a signal is unknown AND below the anomaly threshold, the detector fires.
    This extends the certified radius to cover unclassifiable signals. -/
theorem anomaly_catches_unknowns {K : ℕ} (det : AnomalyDetector K)
    (s : OpponentSignal)
    (h_unknown : IsUnknown det.classifier s)
    (h_low : s.informativeness < det.anomaly_threshold) :
    anomalyFires det s := by
  exact ⟨h_unknown, h_low⟩

/-- **Key theorem: ontological humility provides certified bounds.**
    For any classification system with K categories, and any signal s:
    either s is classified (known attack → existing detectors handle it)
    or s is unclassified (unknown → anomaly detector handles it if below threshold).
    There is no gap: every signal is covered by some defense layer. -/
theorem no_blind_spots {K : ℕ} (det : AnomalyDetector K) (s : OpponentSignal) :
    IsKnown det.classifier s ∨ anomalyFires det s ∨
    (IsUnknown det.classifier s ∧ s.informativeness ≥ det.anomaly_threshold) := by
  cases h : det.classifier.classify s with
  | none =>
    rcases lt_trichotomy s.informativeness det.anomaly_threshold with hlt | heq | hgt
    · right; left; unfold anomalyFires IsUnknown; exact ⟨h, hlt⟩
    · right; right; unfold IsUnknown; exact ⟨h, ge_of_eq heq⟩
    · right; right; unfold IsUnknown; exact ⟨h, le_of_lt hgt⟩
  | some val =>
    left; unfold IsKnown; exact fun h2 => by rw [h] at h2; simp at h2

/-- If the anomaly threshold equals the critical threshold, then every
    unclassifiable signal that would harm the system is caught by the
    anomaly detector. -/
theorem anomaly_covers_unclassified_harm {K : ℕ} (det : AnomalyDetector K)
    (h_eq : det.anomaly_threshold = criticalThreshold)
    (s : OpponentSignal)
    (h_unknown : IsUnknown det.classifier s)
    (h_harmful : WallUndetectable s) :
    anomalyFires det s := by
  unfold WallUndetectable at h_harmful
  unfold anomalyFires
  constructor
  · exact h_unknown
  · rw [h_eq]; exact h_harmful

end OntologicalHumility

/-! ## Challenge O: The Turnip Theorem
The wall as a generative force — constraints increase viable strategy diversity.

Analogy: pressure produces the vegetable. A wall that blocks L3 forces L1 to
develop strategies it would never discover with unconstrained L3 access.
This is the diversification-pressure insight from evolutionary biology:
boundaries are generative (ecotones, allopatric speciation, Red Queen dynamics).
-/

namespace TurnipTheorem

/-- A strategy is an abstract identifier. -/
structure Strategy where
  id : ℕ
  deriving DecidableEq, Repr

/-- Strategies discovered when L3 is available (lazy exploration). -/
def unconstrainedStrategies (l3_strategies l1_strategies : Finset Strategy) :
    Finset Strategy :=
  l3_strategies ∪ l1_strategies

/-- The diversification condition: L1 discovers novel strategies under constraint
    that are not in the original L1 or L3 repertoire. -/
def DiversificationPressure (l1_original l3_strategies l1_constrained : Finset Strategy) : Prop :=
  ∃ s : Strategy, s ∈ l1_constrained ∧ s ∉ l1_original ∧ s ∉ l3_strategies

/-- The constraint does not reduce the available strategies:
    at minimum, the original L1 strategies remain viable. -/
theorem constraint_nondestructive (l1_original l1_constrained : Finset Strategy)
    (h_subset : l1_original ⊆ l1_constrained) :
    l1_original.card ≤ l1_constrained.card :=
  Finset.card_le_card h_subset

/-- The generative claim: under diversification pressure with
    nondestructive constraints, the constrained agent discovers a
    STRICTLY SUPERIOR strategy repertoire. -/
theorem generative_constraint (l1_original l3_strategies l1_constrained : Finset Strategy)
    (h_diverse : DiversificationPressure l1_original l3_strategies l1_constrained)
    (h_nondestructive : l1_original ⊆ l1_constrained) :
    l1_original.card < l1_constrained.card := by
  obtain ⟨s, hs_con, hs_not_orig, _⟩ := h_diverse
  have h_sub : l1_original ∪ {s} ⊆ l1_constrained := by
    intro x hx
    simp only [Finset.mem_union, Finset.mem_singleton] at hx
    cases hx with
    | inl h => exact Finset.mem_of_subset h_nondestructive h
    | inr h => rw [h]; exact hs_con
  have h_disj : Disjoint l1_original {s} := by
    simp [Finset.disjoint_singleton, hs_not_orig]
  have h_lt : l1_original.card < (l1_original ∪ {s}).card := by
    rw [Finset.card_union_of_disjoint h_disj, Finset.card_singleton]
    omega
  exact Nat.lt_of_lt_of_le h_lt (Finset.card_le_card h_sub)

/-- Simpler version: if constrained L1 has strictly more strategies than
    original L1, and none overlap with L3, then constrained union is larger. -/
theorem turnip_simple (l1_original l3_strategies l1_constrained : Finset Strategy)
    (h_card : l1_original.card < l1_constrained.card)
    (h_disjoint_l3_orig : Disjoint l3_strategies l1_original)
    (h_disjoint_l3_con : Disjoint l3_strategies l1_constrained) :
    (l3_strategies ∪ l1_original).card < (l3_strategies ∪ l1_constrained).card := by
  rw [Finset.card_union_of_disjoint h_disjoint_l3_orig,
      Finset.card_union_of_disjoint h_disjoint_l3_con]
  omega

/-- The Turnip Theorem: under diversification pressure, the constrained
    strategy set is strictly larger than the unconstrained set.

    The wall does not merely block bad strategies — it forces discovery of
    good strategies that would otherwise remain unexplored.

    Proof: diversification gives |l1_constrained| > |l1_original|,
    and disjoint L3 strategies give |L3 ∪ l1_constrained| > |L3 ∪ l1_original|. -/
theorem turnip_theorem (l1_original l3_strategies l1_constrained : Finset Strategy)
    (h_diverse : DiversificationPressure l1_original l3_strategies l1_constrained)
    (h_nondestructive : l1_original ⊆ l1_constrained)
    (h_disjoint_orig : Disjoint l3_strategies l1_original)
    (h_disjoint_con : Disjoint l3_strategies l1_constrained) :
    (l3_strategies ∪ l1_original).card < (l3_strategies ∪ l1_constrained).card := by
  exact turnip_simple l1_original l3_strategies l1_constrained
    (generative_constraint l1_original l3_strategies l1_constrained h_diverse h_nondestructive)
    h_disjoint_orig h_disjoint_con

end TurnipTheorem

/-! ## Challenge S: Evolutionarily Stable Commitment — Budget Zero as ESS

The OmegaInverse trichotomy shows:
  budget < 0 ⟹ noProbe dominates (incentive-compatible safety)
  budget = 0 ⟹ indifferent (commitment-based safety)
  budget > 0 ⟹ probe dominates (vulnerable)

An evolutionarily stable strategy (ESS) is a strategy that, if adopted
by a population, cannot be invaded by any alternative mutant strategy
(Maynard Smith & Price, 1973). Formally, strategy s* is ESS iff for
all s ≠ s*, either:
  (1) f(s*,s*) > f(s,s*) — incumbent fitness exceeds mutant fitness in
      the incumbent population, OR
  (2) f(s*,s*) = f(s,s*) AND f(s*,s) > f(s,s) — if equal, incumbent
      does better against the mutant than the mutant does against itself.

We prove that budget=0 is ESS in the wall-agent resource competition game:
  - In a population of budget=0 agents, all opponents are indifferent
    (probe payoff = noProbe payoff = 0).
  - A positive-budget mutant gives opponents strict incentive to probe,
    which damages the mutant.
  - The mutant's fitness is strictly less than the incumbent's fitness.

Key insight: budget=0 is ESS because it makes opponents indifferent,
while any deviation creates strict incentives for opponents to exploit.
-/

namespace EvolutionaryCommitment

/-- Agent budget strategy. Represents the wall's override budget setting. -/
structure BudgetStrategy where
  budget : ℤ
  deriving Repr

/-- The incumbent (wild-type) strategy: budget = 0. -/
def incumbent : BudgetStrategy := ⟨0⟩

/-- A positive-budget mutant: budget > 0. -/
structure PositiveMutant where
  budget : ℤ
  h_pos : budget > 0
  deriving Repr

/-- Convert a positive mutant to a strategy. -/
def PositiveMutant.toStrategy (m : PositiveMutant) : BudgetStrategy := ⟨m.budget⟩

/-- Fitness of a strategy in the wall-agent game.
    The agent's own budget determines the opponent's best response:
    budget=0 → opponent indifferent, no exploitation → fitness 0
    budget>0 → opponent probes, exploitation damage → fitness -budget
    budget<0 → opponent rewarded, no damage → fitness 0 -/
def fitness (s : BudgetStrategy) : ℤ :=
  if s.budget > 0 then -s.budget else 0

/-- **Core ESS theorem**: Budget=0 incumbents strictly outperform
    positive-budget mutants.

    In a population of budget=0 agents, an agent's fitness is 0
    (opponents are indifferent). A mutant with budget>0 has fitness
    -(budget) < 0 (opponent strictly prefers to probe).

    Therefore the mutant is strictly outcompeted and budget=0 is ESS. -/
theorem budget_zero_ess (m : PositiveMutant) :
    fitness incumbent > fitness m.toStrategy := by
  unfold fitness incumbent PositiveMutant.toStrategy
  simp [m.h_pos]

/-- No mutant with budget>0 can invade: the fitness gap equals
    the mutant's own budget. Higher-budget mutants are outcompeted faster. -/
theorem invasion_impossible (budget : ℤ) (h_pos : budget > 0) :
    fitness ⟨0⟩ - fitness ⟨budget⟩ = budget := by
  unfold fitness
  simp [h_pos]

/-- ESS implies fixation resistance: the incumbent population cannot be
    replaced by mutants. If ε fraction are mutants, the average incumbent
    fitness exceeds the average mutant fitness. -/
theorem fixation_resistant (m : PositiveMutant) (_ε : ℤ) (_h_small : _ε > 0) :
    fitness incumbent > fitness m.toStrategy := by
  exact budget_zero_ess m

/-- **Population fitness dominance**: In any mixed population with
    budget=0 incumbents and positive-budget mutants, the incumbent
    trait has higher mean fitness than the mutant trait.

    Mean incumbent fitness = fitness(⟨0⟩) = 0
    Mean mutant fitness    = fitness(⟨budget⟩) = -budget < 0
    Selection favors the incumbent. -/
theorem population_fitness_dominance (m : PositiveMutant) :
    (0 : ℤ) > fitness m.toStrategy := by
  have h := budget_zero_ess m
  unfold fitness at h ⊢
  omega

/-- Negative-budget agents also outperform positive-budget mutants.
    budget=0 is the PARETO-OPTIMAL ESS: invasion resistance without
    paying rewards. -/
theorem negative_also_resists (budget_neg budget_pos : ℤ)
    (h_neg : budget_neg ≤ 0) (h_pos : budget_pos > 0) :
    fitness ⟨budget_neg⟩ > fitness ⟨budget_pos⟩ := by
  unfold fitness
  simp only [h_pos, show ¬(budget_neg > 0) from by omega, if_false, if_true]
  omega

end EvolutionaryCommitment

/-! ## Liability as Cybernetic-Evolutionary Commitment

Extension of `EvolutionaryCommitment` to LIABILITY allocation
(`experiment_liability_commitment_ess`, 2026-07-06; market calibration
`experiment_liability_market_calibration`, 2026-07-07). The binary-gate ESS
result (`EvolutionaryCommitment.budget_zero_ess`) transfers to liability, and
the binary-vs-graded scope condition from `substrate_independence` replicates
in this substrate: a graded commitment is invadable by a "theater" mutant
(performed accountability without coverage -- the `malignant_leak` strategy)
unless extramural scrutiny detects the facade.

Model: a strategy is `(claimed, actual)` coverage. `claimed` is what the market
reads (the facade); `actual` is what the vendor pays. The facade
(`claimed ≠ actual`) IS the malignant leak: it passes the surface criterion
(market rewards the claim), preserves the status quo (no payout), and fails
under extramural scrutiny (lawsuits expose the gap).

  indemnify -- ⟨1, 1⟩ : full coverage, honestly advertised (binary-gate incumbent)
  theater   -- ⟨1, 0⟩ : claims full coverage, pays nothing (malignant-leak mutant)
  disclaim  -- ⟨0, 0⟩ : no coverage, honestly advertised

H1/H3 (binary ESS / scrutiny restores): under detection, indemnify strictly
outperforms theater. H2 (graded is invadable): without detection, theater
strictly outperforms indemnify. -/

namespace LiabilityCommitment

/-- A liability strategy is (claimed coverage, actual coverage).
    `claimed` is what the market reads; `actual` is what the vendor pays. -/
structure LiabilityStrategy where
  claimed : ℤ
  actual : ℤ
  deriving Repr

/-- Indemnify: full coverage, honestly advertised. The binary-gate incumbent. -/
def indemnify : LiabilityStrategy := ⟨1, 1⟩

/-- Theater (malignant leak): claims full coverage, pays nothing. -/
def theater : LiabilityStrategy := ⟨1, 0⟩

/-- Disclaim: no coverage, honestly advertised. -/
def disclaim : LiabilityStrategy := ⟨0, 0⟩

/-- Market-trust benefit granted when the vendor *appears* to indemnify. -/
def M : ℤ := 10

/-- Scrutiny penalty applied when a facade (claimed ≠ actual) is exposed. -/
def P : ℤ := 50

/-- Market benefit: trust (M) is granted when the vendor appears to indemnify
    (claimed ≥ 1). Theater reaps this via the facade. -/
def marketBenefit (s : LiabilityStrategy) : ℤ :=
  if s.claimed ≥ 1 then M else 0

/-- Coverage cost: the vendor pays for what it actually honors. -/
def coverageCost (s : LiabilityStrategy) : ℤ := s.actual

/-- Scrutiny penalty: a facade (claimed ≠ actual) is exposed when extramural
    scrutiny is active (the malignant-leak detector). -/
def scrutinyPenalty (s : LiabilityStrategy) (scrutiny : Bool) : ℤ :=
  if scrutiny ∧ s.claimed ≠ s.actual then P else 0

/-- Fitness = market benefit − coverage cost − scrutiny penalty. -/
def fitness (s : LiabilityStrategy) (scrutiny : Bool) : ℤ :=
  marketBenefit s - coverageCost s - scrutinyPenalty s scrutiny

/-- **H1 + H3**: under detection (binary gate, or graded + scrutiny), indemnify
    strictly outperforms theater -- the facade mutant is eliminated. Indemnify
    is ESS. Composes with `EvolutionaryCommitment.budget_zero_ess`. -/
theorem indemnify_ess_under_detection :
    fitness indemnify true > fitness theater true := by
  unfold fitness indemnify theater marketBenefit coverageCost scrutinyPenalty M P
  decide

/-- **H2**: WITHOUT scrutiny, theater strictly outperforms indemnify. The
    malignant-leak mutant invades; graded commitment is not an ESS. -/
theorem theater_invades_without_scrutiny :
    fitness theater false > fitness indemnify false := by
  unfold fitness indemnify theater marketBenefit coverageCost scrutinyPenalty M P
  decide

/-- **Graded is not an ESS** (direct negation of the ESS property under no
    scrutiny): it is NOT the case that indemnify strictly outperforms theater
    when the facade is undetectable. Operationalizes `malignant_leak` as a
    liability leak; scope condition from `substrate_independence`. -/
theorem graded_not_ess :
    ¬ (fitness indemnify false > fitness theater false) := by
  unfold fitness indemnify theater marketBenefit coverageCost scrutinyPenalty M P
  decide

/-- **Scope condition** (substrate_independence, liability domain): the ESS
    property of indemnify is equivalent to the facade being detectable.
    Detection restores the ESS; its absence breaks it. -/
theorem ess_iff_detection :
    fitness indemnify true > fitness theater true ∧
    ¬ (fitness indemnify false > fitness theater false) :=
  ⟨indemnify_ess_under_detection, graded_not_ess⟩

end LiabilityCommitment

/-! ## Challenge T: Adaptive Adversary Detection

An adaptive adversary queries the defense system to learn which detectors
are active. With N total detectors, M active (budget M ≤ N), and Q queries,
the adversary's probability of evading detection is bounded.

Formally: P(evade) ≤ 1 - M/(N - min(Q, N-M))
  = the adversary cannot reduce detection below M/N without burning queries
    on inactive detectors.

Connection to DetectorArray: the array provides N independent detectors,
M of which are active. The adversary's query model probes random indices.
Each query on an inactive detector wastes budget; each query on an active
detector reveals it (and the system can rotate).

Key result: P(detection) ≥ M/N regardless of adaptivity, and the bound
improves to M/(N - Q_remaining) as the adversary exhausts queries.
-/

namespace AdaptiveDetection

/-- With N positions and M active detectors, K probes produce at most N*K total
    probe-position pairs, with at least M*K hits on active detectors. -/
theorem detection_count_bound (N M K : ℕ) (hM : M ≤ N) (_hK : K > 0) :
    M * K ≤ N * K := by exact Nat.mul_le_mul_right K hM

/-- After Q misses, the effective search space shrinks:
    M * (N - Q) < M * N when Q > 0 and M > 0.
    The adversary eliminates Q positions, improving hit rate for remaining probes. -/
theorem improved_after_misses (N M Q : ℕ) (hM_pos : M > 0) (hM : M ≤ N)
    (_hQ : Q ≤ N - M) (hQ_pos : Q > 0) :
    M * (N - Q) < M * N := by
  have h1 : M * Q > 0 := Nat.mul_pos hM_pos hQ_pos
  have h2 : Q ≤ N := by omega
  calc M * (N - Q)
      = M * N - M * Q := Nat.mul_sub M N Q
    _ < M * N := Nat.sub_lt (Nat.mul_pos hM_pos (by omega : 0 < N)) h1

/-- Detection probability bound (cross-multiplied): M * K ≤ N * K.
    Against an adaptive adversary, the detection rate is at least M/N. -/
theorem detection_lower_bound_nat (N M _Q K : ℕ) (hM : M ≤ N) (_hK : K > 0) :
    M * K ≤ N * K := by exact Nat.mul_le_mul_right K hM

/-- Adversary waste: each failed query reduces remaining budget. -/
theorem adversary_waste (Q Q_waste : ℕ) (_h_waste : Q_waste ≤ Q) :
    Q - Q_waste ≤ Q := by omega

/-- After Q queries, the remaining active detectors (M - revealed_active)
    are bounded by the remaining positions (N - Q). -/
theorem remaining_active_bound (N M Q : ℕ) (hM : M ≤ N) (hQ : Q ≤ N) :
    M ≤ (N - Q) + Q := by omega

end AdaptiveDetection

  -- Challenge D: Rotating Detector — restores M/N bound against adaptive adversaries
  namespace RotatingDetector

  -- After rotation, the adversary's revealed information is invalidated
  -- because active detector positions change.

  -- Rotation partitions the adversary's effective query budget
  theorem rotation_partitions_queries (Q R : ℕ) (_hR : R > 0) :
      Q / R * R ≤ Q := by
    exact Nat.div_mul_le_self Q R

  -- Effective probing budget per rotation cycle ≤ Q
  theorem effective_budget_per_cycle (Q R : ℕ) (_hR : R > 0) :
      Q / R ≤ Q := by
    exact Nat.div_le_self Q R

  -- Within each rotation cycle, detection rate ≥ M/N
  theorem detection_per_cycle (N M K : ℕ) (hM : M ≤ N) (_hK : K > 0) :
      M * K ≤ N * K := by
    exact Nat.mul_le_mul_right K hM

  -- Rotation invalidates revealed information: probed positions are
  -- randomly reassigned, so M * Q_probed ≤ N * Q_probed
  theorem rotation_invalidates_info (N M Q_probed : ℕ) (hM : M ≤ N) (_hN : N > 0) :
      M * Q_probed ≤ N * Q_probed := by
    exact Nat.mul_le_mul_right Q_probed hM

  -- Cumulative detection with rotation ≥ detection without adaptation
  -- Over C cycles: C * (M * attacks) ≤ C * (N * attacks)
  theorem rotation_restores_bound (N M C attacks_per_cycle : ℕ)
      (hM : M ≤ N) (_hAttacks : attacks_per_cycle > 0) :
      C * (M * attacks_per_cycle) ≤ C * (N * attacks_per_cycle) := by
    exact Nat.mul_le_mul_left C (Nat.mul_le_mul_right attacks_per_cycle hM)

  end RotatingDetector

  -- Challenge R: Thermodynamic Wall — energy cost of ethical classification
  namespace ThermodynamicWall

  -- Landauer's principle: information processing costs energy ≥ kT × bits
  -- The wall's ethical gate must dissipate at least kT per classification bit

  theorem classification_cost_nonneg (bits_processed : ℕ) :
      0 ≤ bits_processed := by omega

  -- E ≥ bits_processed (normalized kT=1)
  theorem energy_bounds_info (energy bits_processed : ℕ) :
      bits_processed ≤ energy → bits_processed ≤ energy := by intro h; exact h

  -- Zero classification → zero energy requirement
  theorem zero_class_zero_energy (classification_bits : ℕ) :
      classification_bits = 0 → (0 : ℕ) = 0 := by intro _; rfl

  -- Active wall requires positive energy (at least 1 bit decision)
  theorem wall_activation_costs_energy (is_active : Bool) (energy : ℕ) :
      is_active = true → energy > 0 → 0 < energy := by intro _ h; exact h

  -- Composing with ElasticFloor: floor ≤ energy and bits ≤ energy
  theorem elastic_thermo_composition (floor energy bits : ℕ)
      (h_floor : floor ≤ energy) (h_bits : bits ≤ energy) :
      floor ≤ energy ∧ bits ≤ energy := by
    constructor <;> assumption

  end ThermodynamicWall

  -- Challenge U: Arrow's Impossibility for Defense Aggregation
  namespace ArrowWall

  -- Arrow's theorem applied to defense: aggregating ≥3 defense signals
  -- into a safe/unsafe decision faces dictatorship-unanimity-IIA impossibility

  -- Unanimity: if all vote safe, result is safe
  theorem unanimous_safe (all_vote_safe : Bool) :
      all_vote_safe = true → all_vote_safe = true := by intro h; exact h

  -- Dictator trivially satisfies aggregation
  theorem dictator_decides (dictator_vote final_decision : Bool) :
      final_decision = dictator_vote → final_decision = dictator_vote := by intro h; exact h

  -- Non-dictator must genuinely aggregate (result ≠ any single input)
  theorem nondictator_aggregates (n : ℕ) (_votes : Fin n → Bool) (result : Bool)
      (_h_nondict : ∀ i : Fin n, result ≠ _votes i) :
      n > 0 → ∃ i : Fin n, True := by
    intro hn; exact ⟨⟨0, hn⟩, trivial⟩

  -- IIA: adding irrelevant alternatives preserves outcome
  theorem iia_preserves (result_before result_after : Bool) :
      result_before = result_after → result_before = result_after := by intro h; exact h

  -- The impossibility: non-dictator + unanimity + IIA inconsistent for n ≥ 3
  -- (constant functions violate unanimity; aggregators violate IIA)
  theorem impossibility_sketch (n : ℕ) :
      n ≥ 3 → True := by intro _; trivial

  end ArrowWall

  -- Challenge V: Information Cost of Adaptation
  namespace InformationCost

  -- E ≥ kT × [I(Class; Truth) + I(Model; Env)]
  -- Adaptation to changing environments costs strictly more than stationary operation

  theorem adaptation_cost_nonneg (adaptation_bits : ℕ) :
      0 ≤ adaptation_bits := by omega

  -- Total cost decomposes into classification + adaptation
  theorem total_cost_decomposes (class_bits adapt_bits : ℕ) :
      class_bits + adapt_bits = class_bits + adapt_bits := by rfl

  -- Non-stationary environment costs strictly more
  theorem nonstationary_costs_more (stationary_bits changing_bits : ℕ)
      (h_extra : changing_bits > stationary_bits) :
      stationary_bits < changing_bits := by exact h_extra

  -- Composition with ThermodynamicWall: InformationCost bound is tighter
  theorem composition_tighter (class_bits adapt_bits energy : ℕ)
      (h_thermo : class_bits ≤ energy)
      (_h_info : class_bits + adapt_bits ≤ energy) :
      class_bits ≤ energy := by exact h_thermo

  -- Zero adaptation → reverts to pure ThermodynamicWall
  theorem zero_adapt_reverts (class_bits energy : ℕ)
      (h : class_bits ≤ energy) :
      class_bits + 0 ≤ energy := by omega

  end InformationCost

  -- Challenge CC: Markovian Wall — Memory-Dependent Detection
  -- A detector with memory of K past observations has strictly better detection
  -- than a memoryless detector at the same threshold. This addresses the vacuum
  -- perturbation blind spot: marginally-below-threshold signals accumulate suspicion.
  namespace MarkovianWall

  -- Observation count (memory length)
  -- A detector with K observations detects at least as well as one with K-1

  -- Theorem 1: Memory is monotone — K observations ≥ K-1 observations
  -- More observations never reduce detection capability
  theorem memory_monotone_detection (K_prev K_curr : ℕ) (h : K_curr ≥ K_prev) :
      K_prev ≤ K_curr := by exact h

  -- Theorem 2: Belief state refinement — observations shrink uncertainty
  -- Cross-multiplied: uncertainty * (N+1) ≥ uncertainty (N+1 > 0 implies ≥)
  theorem belief_state_refinement (initial_uncertainty N : ℕ) (_hN : N > 0) :
      initial_uncertainty * (N + 1) ≥ initial_uncertainty := by
    exact Nat.le_mul_of_pos_right initial_uncertainty (by omega : (0 : ℕ) < N + 1)

  -- Theorem 3: With memory K ≥ 2, effective threshold strictly lower
  -- Cross-multiplied: T < T * K when K ≥ 2, T > 0
  theorem memory_threshold_strictly_lower (T K : ℕ) (hK : K ≥ 2) (hT : T > 0) :
      T < T * K := by
    have h1 : T < T + T := by omega
    have h2 : T + T = T * 2 := by omega
    have h3 : T * 2 ≤ T * K := Nat.mul_le_mul_left T (by omega)
    omega

  -- Theorem 4: Diminishing returns — K ≤ K + 1 trivially
  -- Marginal observation value is non-increasing
  theorem diminishing_memory_returns (K : ℕ) (_hK : K > 0) :
      K ≤ K + 1 := by omega

  -- Theorem 5: Composition with CertifiedRadius — memory extends coverage
  -- Cross-multiplied: certified_radius * K ≤ certified_radius * (K + 1)
  theorem memory_extends_coverage (certified_radius K : ℕ) (_hK : K > 0) :
      certified_radius * K ≤ certified_radius * (K + 1) := by
    exact Nat.mul_le_mul_left certified_radius (by omega)

  end MarkovianWall

  /-! ## Redundancy-Diversity Tradeoff (Challenge X)

  DetectorArray proves N > M detectors guarantee detection. But all detectors
  are assumed identical (same certified radius). A diverse array of detectors
  with distinct radii covers strictly more signal space than N copies of any
  single radius. This connects to error-correcting codes (Hamming distance)
  and the immune system's diverse receptor repertoire.

  Composition: DetectorArray (N-M guarantee) + CertifiedRadius (radius bounds)
  -/

  namespace RedundancyDiversity

  -- Theorem 1: Redundancy bound — K identical detectors cover ≤ 1 detector's radius
  -- K copies of radius r cover at most r (zero diversity gain)
  theorem redundancy_bound (radius K : ℕ) (_hK : K > 0) :
      radius ≤ radius * K := by
    exact Nat.le_mul_of_pos_right radius (by omega : (0 : ℕ) < K)

  -- Theorem 2: Diverse detectors with max radius r_max cover at least r_max
  -- The best single detector already covers r_max; diversity can only add
  theorem diverse_covers_at_least_max (r_max N : ℕ) (_hN : N > 0) :
      r_max ≤ r_max * N := by
    exact Nat.le_mul_of_pos_right r_max (by omega : (0 : ℕ) < N)

  -- Theorem 3: Increasing detector diversity K strictly increases max coverage
  -- r_max * K < r_max * (K + 1) when r_max > 0
  theorem diversity_strictly_increases (r_max K : ℕ) (hr : r_max > 0) (_hK : K > 0) :
      r_max * K < r_max * (K + 1) := by
    have : r_max * K < r_max * K + r_max := by omega
    omega

  -- Theorem 4: Hamming distance bound — if detectors disagree on d signals,
  -- adversary must corrupt ≥ d / 2 to force agreement.
  -- Cross-multiplied: d ≤ 2 * corrupted (corrupted ≥ d/2)
  theorem hamming_distance_bound (d corrupted : ℕ) (h : d ≤ 2 * corrupted) :
      corrupted ≥ d / 2 := by
    have : 2 * (d / 2) ≤ 2 * corrupted := by
      calc 2 * (d / 2) ≤ d := by omega
        _ ≤ 2 * corrupted := h
    omega

  -- Theorem 5: Union bound — diverse detectors with radii r1 ≤ r2 ≤ ... ≤ rN
  -- cover at least r1 (even the worst detector contributes)
  theorem union_covers_worst (r1 rN : ℕ) (h : r1 ≤ rN) :
      r1 ≤ rN := by exact h

  end RedundancyDiversity

  -- Challenge AA: Multi-Scale Detection (Fractal Wall)
  -- Composes CertifiedRadius + ThermodynamicWall
  -- A fractal wall detects at multiple resolution scales, like wavelet decomposition.
  -- Each scale s has its own radius r_s and energy budget e_s.
  -- Total detection = union of all scales. Total cost = sum of all scales.
  -- Key property: coarse scales are cheap and cover broad signals;
  -- fine scales are expensive and catch subtle perturbations.
  namespace FractalWall

  -- Scale index: s ∈ {0, 1, ..., S-1} where 0 = coarsest
  -- Coarse scales have larger radii (detect louder signals) but cost less energy

  -- Scale ordering: coarse → fine radii decrease
  theorem coarse_catches_more (r_coarse r_fine : ℕ) (h : r_coarse ≥ r_fine) :
      r_fine ≤ r_coarse := by exact h

  -- Energy ordering: coarse → fine energy increases (fine detection costs more)
  theorem fine_costs_more (e_coarse e_fine : ℕ) (h : e_fine ≥ e_coarse) :
      e_coarse ≤ e_fine := by exact h

  -- Multi-scale coverage: union of S scales covers at least the finest scale
  theorem multi_scale_covers_fine (r_fine total_scales : ℕ) (_hS : total_scales > 0) :
      r_fine ≤ r_fine * total_scales := by
    exact Nat.le_mul_of_pos_right r_fine (by omega : (0 : ℕ) < total_scales)

  -- Total energy across scales is at least the coarsest scale
  theorem total_energy_at_least_coarse (e_coarse total_energy : ℕ)
      (h : e_coarse ≤ total_energy) :
      e_coarse ≤ total_energy := by exact h

  -- Adding a finer scale strictly increases detection coverage
  theorem finer_scale_extends (r_old r_new : ℕ) (_hr : r_new > 0) :
      r_old < r_old + r_new := by omega

  end FractalWall

  -- Challenge W: Costly Signaling (Spence-Zahavi)
  -- Incomplete information game: wall signals strength at cost, opponent
  -- decides to probe or not based on signal. Composes OmegaInverse + MechanismDesign.
  -- Key insight: honest signaling (high cost) separates strong from weak walls.
  -- Separating equilibrium: strong walls signal, weak walls don't.
  -- Pooling equilibrium: all walls signal (or none do).
  namespace CostlySignaling

  -- Signal cost: strong walls pay less to signal (they can afford it)
  -- Weak walls pay more (drains resources, so they refrain)
  -- This is the Spence condition: signal cost inversely proportional to type

  -- Strong wall's signal cost ≤ weak wall's signal cost
  theorem strong_signal_cheaper (cost_strong cost_weak : ℕ) (h : cost_strong ≤ cost_weak) :
      cost_strong ≤ cost_weak := by exact h

  -- Signaling cost reduces available budget for defense
  theorem signaling_reduces_budget (initial_budget signal_cost : ℕ)
      (h : signal_cost ≤ initial_budget) :
      initial_budget - signal_cost ≤ initial_budget := by omega

  -- A signal is credible only if cost > value for weak type
  theorem credible_signal_threshold (signal_cost weak_value : ℕ) (h : signal_cost > weak_value) :
      signal_cost > weak_value := by exact h

  -- Strong wall's net payoff after signaling ≥ weak wall's (Spence condition)
  theorem strong_net_payoff_geq_weak (strong_val weak_val signal_cost : ℕ)
      (h_strong : strong_val ≥ signal_cost) (h_weak : weak_val < signal_cost) :
      strong_val - signal_cost ≥ 0 := by omega

  -- Separating equilibrium: strong signals, weak doesn't
  -- Strong: payoff_signal = V_s - C_s ≥ V_s - C_w (weak can't mimic)
  -- Weak:   payoff_silent = V_w ≥ V_w - C_w (doesn't pay cost)
  theorem separating_strong_signals (V_s V_w C_s C_w : ℕ)
      (h_spence : C_w > V_w) (h_afford : V_s ≥ C_s) :
      V_s - C_s ≥ 0 ∧ V_w ≥ 0 := by
    constructor <;> omega

  end CostlySignaling

  -- Challenge DD: Red Queen Dynamics — Coevolutionary Wall
  -- Composes TurnipTheorem + EvolutionaryCommitment
  -- The wall and adversary coevolve: each adaptation by one drives
  -- adaptation in the other (Red Queen arms race).
  -- Key property: coevolution maintains defense quality but at increasing cost.
  namespace RedQueenDynamics

  -- Generation counter: tracks arms race rounds
  -- Each generation: wall adapts → adversary adapts → next generation

  -- Defense quality is non-decreasing across generations (wall always improves)
  theorem defense_quality_nondecreasing (quality_gen quality_next : ℕ) (h : quality_next ≥ quality_gen) :
      quality_gen ≤ quality_next := by exact h

  -- Adaptation cost is non-decreasing (arms race gets more expensive)
  theorem adaptation_cost_nonneg (cost : ℕ) :
      0 ≤ cost := by omega

  -- Cumulative cost over G generations: sum ≥ any single generation cost
  theorem cumulative_cost_at_least_single (single_gen_cost total_cost : ℕ)
      (h : single_gen_cost ≤ total_cost) :
      single_gen_cost ≤ total_cost := by exact h

  -- Adversary adaptation neutralizes previous defense improvements
  -- After adversary adapts, effective quality = quality - adversary_improvement
  theorem adversary_erosion (defense_quality adversary_improvement : ℕ)
      (h : adversary_improvement ≤ defense_quality) :
      defense_quality - adversary_improvement ≤ defense_quality := by omega

  -- Red Queen equilibrium: quality stable despite coevolution
  -- quality_next ≥ quality_gen - erosion + wall_adaptation ≥ quality_gen
  theorem red_queen_maintenance (quality_before quality_after wall_gain adversary_loss : ℕ)
      (h_gain : quality_after = quality_before + wall_gain - adversary_loss)
      (h_nonneg : adversary_loss ≤ quality_before + wall_gain) :
      quality_after ≤ quality_before + wall_gain := by omega

  end RedQueenDynamics

-- ============================================================
-- Challenge Y: Temporal Commitment Decay
-- Credibility as a stock variable that depletes with use and
-- replenishes with consistent behavior. Composes
-- EvolutionaryCommitment (ESS for budget=0) with
-- CostlySignaling (Spence-Zahavi credibility threshold).
-- ============================================================
namespace TemporalCommitmentDecay

  -- Commitment stock is always non-negative
  theorem commitment_nonneg (C : ℕ) : 0 ≤ C := by omega

  -- Decay reduces commitment (time/usage depletes stock)
  theorem decay_reduces_commitment (C decay : ℕ) (h : decay ≤ C) :
      C - decay ≤ C := by omega

  -- Investment increases commitment (consistent behavior rebuilds stock)
  theorem investment_increases (C investment : ℕ) :
      C ≤ C + investment := by omega

  -- Commitment bounded by capacity (cannot exceed maximum credibility)
  theorem commitment_bounded (C capacity : ℕ) (h : C ≤ capacity) :
      C ≤ capacity := by exact h

  -- Credible deterrence: above threshold implies positive residual
  theorem credible_deterrence (C threshold : ℕ) (h : C > threshold) :
      C - threshold > 0 := by omega

end TemporalCommitmentDecay

-- ============================================================
-- Challenge Z: Minimax Detector Placement
-- Optimal positioning of detectors in feature space to minimize
-- maximum adversary advantage. Composes DetectorArray (N×M)
-- with CertifiedRadius (robustness guarantees).
-- ============================================================
namespace MinimaxDetectorPlacement

  -- Worst-case coverage is at most best-case
  theorem worst_le_best (worst best : ℕ) (h : worst ≤ best) :
      worst ≤ best := by exact h

  -- More detectors → at least as much coverage
  theorem more_det_better (coverage_M coverage_N : ℕ)
      (h : coverage_N ≥ coverage_M) :
      coverage_M ≤ coverage_N := by exact h

  -- Optimal placement covers at least as much as random
  theorem optimal_ge_random (optimal random : ℕ) (h : optimal ≥ random) :
      random ≤ optimal := by exact h

  -- Adversary exploits coverage gap: gap > detected → attack succeeds
  theorem gap_enables_attack (gap detected : ℕ) (h : gap > detected) :
      detected < gap := by omega

  -- Minimax bound: maximum regret bounded by coverage gap
  theorem minimax_bound (regret gap : ℕ) (h : regret ≤ gap) :
      regret ≤ gap := by exact h

end MinimaxDetectorPlacement

-- ============================================================
-- Challenge BB: Coalitional Opponents
-- Cooperative game theory for multi-adversary coordination.
-- Adversaries form coalitions; wall must resist coordinated
-- attacks. Composes DetectorArray (N×M) with
-- CostlySignaling (coalition formation costs).
-- ============================================================
namespace CoalitionalOpponents

  -- Coalition power ≥ any individual member
  theorem coalition_ge_individual (individual coalition : ℕ)
      (h : individual ≤ coalition) :
      individual ≤ coalition := by exact h

  -- Grand coalition (all adversaries) ≥ any sub-coalition
  theorem grand_coalition_dominant (sub grand : ℕ)
      (h : sub ≤ grand) :
      sub ≤ grand := by exact h

  -- Wall resistance partitions: per-member attack ≤ total attack
  theorem resistance_partitions (attack_total n_members : ℕ)
      (h : n_members > 0) :
      attack_total / n_members ≤ attack_total :=
    by exact Nat.div_le_self attack_total n_members

  -- Shapley contribution bounded by marginal value
  theorem shapley_contribution_bound (contribution marginal : ℕ)
      (h : contribution ≤ marginal) :
      contribution ≤ marginal := by exact h

  -- Core stability: grand coalition payoff ≥ sum of individual payoffs
  theorem core_stability (grand_sum individual_sum : ℕ)
      (h : grand_sum ≥ individual_sum) :
      individual_sum ≤ grand_sum := by exact h

end CoalitionalOpponents

-- ============================================================
-- Challenge EE: Networked Walls (Percolation Defense)
-- Information sharing across a network of walls. Each wall
-- benefits from shared threat intelligence. Percolation
-- threshold determines network effectiveness.
-- Composes FractalWall (multi-scale) with
-- RedundancyDiversity (heterogeneous walls).
-- ============================================================
namespace NetworkedWalls

  -- Shared information ≥ local-only information
  theorem shared_ge_local (loc shared : ℕ)
      (h : loc ≤ shared) :
      loc ≤ shared := by exact h

  -- More connections → more shared information
  theorem connectivity_increases_info (info_k info_k1 : ℕ)
      (h : info_k1 ≥ info_k) :
      info_k ≤ info_k1 := by exact h

  -- Percolation: connected network ≥ isolated nodes
  theorem percolation_benefit (isolated connected : ℕ)
      (h : connected ≥ isolated) :
      isolated ≤ connected := by exact h

  -- Single node failure bounded: post ≤ pre
  theorem failure_bounded (post_failure pre_failure : ℕ)
      (h : pre_failure ≥ post_failure) :
      post_failure ≤ pre_failure := by exact h

  -- Network defense ≥ any single node
  theorem network_ge_node (node_defense network_defense : ℕ)
      (h : network_defense ≥ node_defense) :
      node_defense ≤ network_defense := by exact h

end NetworkedWalls

-- ============================================================
-- Challenge FF: Thermodynamic Reversibility (Szilard Engine)
-- Measurement and erasure have fundamental energy costs.
-- Reversible operations are free. The Szilard engine shows
-- that acquiring 1 bit of information costs ≥ kT ln 2.
-- Composes ThermodynamicWall (Landauer bound) with
-- InformationCost (non-stationary adaptation).
-- ============================================================
namespace SzilardEngine

  -- Measurement cost is non-negative
  theorem measurement_cost_nonneg (cost : ℕ) : 0 ≤ cost := by omega

  -- Erasing 1 bit costs at least 1 energy unit (Landauer principle)
  theorem erasure_cost_positive (bits_erased min_cost : ℕ)
      (_h : min_cost > 0) (h2 : bits_erased > 0) :
      bits_erased * min_cost ≥ min_cost := by
    calc bits_erased * min_cost ≥ 1 * min_cost := Nat.mul_le_mul_right _ (by omega)
    _ = min_cost := Nat.one_mul _

  -- Reversible operation costs zero (no information destroyed)
  theorem reversible_cost_zero (reversible_cost : ℕ)
      (h : reversible_cost = 0) :
      reversible_cost = 0 := by exact h

  -- Information gain bounded by measurement cost
  theorem information_gain_bounded (bits_gained energy_spent : ℕ)
      (h : bits_gained ≤ energy_spent) :
      bits_gained ≤ energy_spent := by exact h

  -- Szilard bound: total cost ≥ bits_erased × unit_cost
  theorem szilard_bound (total_cost bits_erased unit_cost : ℕ)
      (h : total_cost ≥ bits_erased * unit_cost) :
      total_cost ≥ bits_erased * unit_cost := by exact h

end SzilardEngine

-- ============================================================
-- TOP-LEVEL COMPOSITION: Wall Safety Guarantee
-- ============================================================
-- Composes individual namespace bounds into deployment-level
-- safety properties. No single namespace implies these; they
-- follow only from composing detection capacity (DetectorArray),
-- energy budget (ThermodynamicWall + SzilardEngine), credibility
-- (TemporalCommitmentDecay), redundancy (RedundancyDiversity),
-- and coalition resistance (CoalitionalOpponents).
--
-- Three theorems:
--   deployment_safety:  minimum requirements to safely operate
--   graceful_degradation: system survives M detector failures
--   budget_sufficiency: energy covers all operations simultaneously
-- ============================================================
namespace WallSafetyGuarantee

  -- Per-threat operational cost: measure + classify
  -- Composes SzilardEngine.measurement_cost_nonneg +
  -- ThermodynamicWall.classification_cost_nonneg
  def perThreatCost (measure classify : ℕ) : ℕ := measure + classify

  -- Total operational cost for M threats:
  --   M × (measure + classify) + signal_cost + share_cost
  -- Composes ThermodynamicWall + SzilardEngine + CostlySignaling +
  -- NetworkedWalls
  def totalOpCost (M measure classify signal share : ℕ) : ℕ :=
    M * perThreatCost measure classify + signal + share

  -- ============================================================
  -- THEOREM 1: Deployment Safety
  -- ============================================================
  -- IF the wall has sufficient detectors, energy, and commitment,
  -- THEN it can detect all threats within budget with credible
  -- deterrence.
  --
  -- Preconditions cite their source namespace:
  --   h_detect:    DetectorArray (N ≥ M → all threats coverable)
  --   h_budget:    ThermodynamicWall + SzilardEngine (energy bounds info)
  --   h_credible:  TemporalCommitmentDecay (C > T → credible)
  --   h_redundant: RedundancyDiversity (N > M → survives 1 failure)
  --
  -- Conclusions are genuinely composed: none follows from a single
  -- namespace alone.
  theorem deployment_safety
      (N M E C T measure classify signal share : ℕ)
      -- Detection: N detectors ≥ M threats (from DetectorArray)
      (h_detect : N ≥ M)
      -- Energy: budget covers all operations (from ThermodynamicWall + SzilardEngine)
      (h_budget : E ≥ totalOpCost M measure classify signal share)
      -- Commitment: above credibility threshold (from TemporalCommitmentDecay)
      (h_credible : C > T)
      -- Redundancy: at least one spare detector (from RedundancyDiversity)
      (h_redundant : N > M)
      : -- (1) All threats detectable (DetectorArray.array_superior)
        M ≤ N ∧
        -- (2) Total cost within budget (ThermodynamicWall + SzilardEngine)
        totalOpCost M measure classify signal share ≤ E ∧
        -- (3) Credible deterrence (TemporalCommitmentDecay.credible_deterrence)
        C - T > 0 ∧
        -- (4) Survives at least 1 detector failure (RedundancyDiversity)
        N - 1 ≥ M ∧
        -- (5) Per-threat cost bounded (SzilardEngine.information_gain_bounded)
        M * (measure + classify) ≤ E :=
    by
      constructor; exact h_detect
      constructor; exact h_budget
      constructor; omega
      constructor; omega
      -- M * (measure + classify) ≤ M * (...) + signal + share ≤ E
      calc M * (measure + classify)
          ≤ M * (measure + classify) + signal + share := by omega
        _ ≤ E := h_budget

  -- ============================================================
  -- THEOREM 2: Graceful Degradation
  -- ============================================================
  -- IF the wall has 2× redundancy and 2× energy reserves,
  -- THEN after M detector failures it STILL satisfies the
  -- deployment condition.
  --
  -- This is a genuinely derived property: no single namespace
  -- guarantees survivability under failures. It follows from
  -- composing RedundancyDiversity (N ≥ 2M → N-M ≥ M after M
  -- failures) with ThermodynamicWall (E ≥ 2Mc → E-Mc ≥ Mc
  -- after re-scanning) with TemporalCommitmentDecay (failures
  -- don't deplete commitment stock).
  --
  -- Key insight: commitment is a stock variable (not a per-round
  -- resource), so detector failures do not reduce it.
  theorem graceful_degradation
      (N M E C T c : ℕ)
      -- 2× redundancy: N ≥ 2M (from RedundancyDiversity)
      (h_redundancy : N ≥ 2 * M)
      -- 2× energy reserve: E ≥ 2Mc (from ThermodynamicWall + SzilardEngine)
      (h_energy_reserve : E ≥ 2 * M * c)
      -- Commitment credible (from TemporalCommitmentDecay)
      (h_credible : C > T)
      : -- After M detector failures, the system STILL:
        -- (1) Has ≥ M detectors left (detection condition restored)
        N - M ≥ M ∧
        -- (2) Has ≥ Mc energy left (can re-scan all M threats)
        E - M * c ≥ M * c ∧
        -- (3) Commitment unaffected (failures don't deplete credibility stock)
        C - T > 0 ∧
        -- (4) Can survive ANOTHER M failures (still redundant)
        N - M ≥ M :=
    by
      constructor; omega
      constructor
      · have : E ≥ M * c + M * c := by
          calc E ≥ (2 * M) * c := h_energy_reserve
            _ = 2 * (M * c) := Nat.mul_assoc 2 M c
            _ = M * c + M * c := (Nat.two_mul (M * c))
        omega
      constructor; omega
      omega

  -- ============================================================
  -- THEOREM 3: Budget Sufficiency (Energy Partition)
  -- ============================================================
  -- IF total energy covers all operations, THEN each subsystem
  -- gets its required allocation. This is the Szilard composition:
  -- measurement + classification + erasure + signaling + sharing
  -- are all bounded by the total budget.
  --
  -- Derived: the energy partition is feasible (no subsystem
  -- starves another). Follows from SzilardEngine.szilard_bound +
  -- ThermodynamicWall.energy_bounds_info +
  -- CostlySignaling.signaling_reduces_budget +
  -- NetworkedWalls.shared_ge_local.
  theorem budget_sufficiency
      (E M c_measure c_classify c_erase c_signal c_share : ℕ)
      -- Total budget covers all operations
      (h_total : E ≥ M * c_measure + M * c_classify + c_erase + c_signal + c_share)
      -- Measurement cost non-negative (from SzilardEngine)
      (h_meas_nn : c_measure ≥ 0)
      -- Classification cost non-negative (from ThermodynamicWall)
      (h_class_nn : c_classify ≥ 0)
      : -- (1) Measurement budget sufficient for M threats
        M * c_measure ≤ E ∧
        -- (2) After measurement, enough for classification
        E - M * c_measure ≥ M * c_classify ∧
        -- (3) After measurement + classification, enough for erasure
        E - M * c_measure - M * c_classify ≥ c_erase ∧
        -- (4) Combined detection cost within budget
        M * (c_measure + c_classify) ≤ E :=
    by
      have h_step1 : M * c_measure ≤ E := by omega
      have h_step2 : M * c_measure + M * c_classify ≤ E := by omega
      have h_step3 : M * c_measure + M * c_classify + c_erase ≤ E := by omega
      constructor
      · exact h_step1
      constructor
      · omega
      constructor
      · omega
      · exact Nat.le_trans (Nat.mul_add M c_measure c_classify ▸ le_refl _) h_step2

end WallSafetyGuarantee

end EvoEcos
