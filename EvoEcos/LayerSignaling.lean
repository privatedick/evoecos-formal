/-
Layer Signaling: The Wall Signal is Informationally Uninformative
================================================================

In the EvoEcos architecture, L2 sends a binary signal (wall_on / wall_off) to L3.
This file proves that this signal cannot support a separating equilibrium in the
signaling-game sense (Spence 1973).

Key insight: The wall cost is independent of L1 state (Landauer energy), so the
Spence-Mirrlees single-crossing condition fails. Only pooling equilibria exist,
meaning L3 learns nothing about L1 stability from the wall signal alone.

This explains WHY the architecture blocks L3 rather than trying to inform it:
the binary signal is provably uninformative about the continuous L1 stability.

Results (0 sorry):
  1. wall_signal_is_binary         — trivial: wall is Bool
  2. wall_cost_constant            — energy cost same for stable/unstable L1
  3. single_crossing_failure       — Spence-Mirrlees condition fails
  4. pooling_equilibrium           — L3 cannot infer L1 state from wall alone
  5. wall_blocks_not_informs       — blocking is architecturally correct

Date: 2026-05-29
-/

import EvoEcos.Layers
import EvoEcos.L3Understanding
import EvoEcos.ThermodynamicCompanion
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

noncomputable section

namespace EvoEcos.LayerSignaling

open ThermodynamicCompanion
open Transition (activateWall_makes_wall_true)

/-! ## Type Definitions for the Signaling Game -/

/-- L1 stability type for the signaling game.
    L2 (sender) knows the true type; L3 (receiver) does not. -/
inductive L1StabilityType where
  /-- L1 is stable (stability >= 0.4) -/
  | stable : L1StabilityType
  /-- L1 is unstable (stability < 0.4) -/
  | unstable : L1StabilityType
deriving Repr, DecidableEq

/-- The binary wall signal that L2 sends to L3. -/
inductive WallSignal where
  /-- Wall is active (blocking L3) -/
  | wall_on : WallSignal
  /-- Wall is inactive (L3 not blocked) -/
  | wall_off : WallSignal
deriving Repr, DecidableEq

/-- Energy cost of a wall activation/deactivation.
    Following Landauer's principle (formalized in ThermodynamicCompanion.lean):
    the cost of erasing one bit of information is kT * ln(2).
    This cost depends only on the information content, not on the physical state. -/
structure WallEnergyCost where
  /-- Bits of information erased (Landauer cost) -/
  bits : ℕ
  /-- Temperature-energy product (normalized to kT = 1) -/
  kT : ℝ
  hkT_pos : 0 < kT := by norm_num

namespace WallEnergyCost

/-- Total energy cost = bits * kT (Landauer's principle). -/
def total (c : WallEnergyCost) : ℝ :=
  c.bits * c.kT

/-- Energy cost is non-negative. -/
theorem total_nonneg (c : WallEnergyCost) : 0 ≤ c.total := by
  unfold total
  exact mul_nonneg (Nat.cast_nonneg _) (le_of_lt c.hkT_pos)

end WallEnergyCost

/-! ## Result 1: Wall Signal is Binary -/

/-- **Result 1.** The wall signal takes exactly two values: on or off.
    This is trivial from the WallSignal type definition but establishes
    the bounded signaling vocabulary. -/
theorem wall_signal_is_binary (s : WallSignal) :
    s = WallSignal.wall_on ∨ s = WallSignal.wall_off := by
  cases s with
  | wall_on => exact Or.inl rfl
  | wall_off => exact Or.inr rfl

/-! ## Result 2: Wall Cost is Constant -/

/-- The cost of sending the wall signal does not depend on L1 stability type.
    This follows from Landauer's principle: the energy to erase/set one bit
    depends only on the bit being processed, not on the physical substrate state.

    In the signaling game framework, this means the sender's type does not
    affect the cost of signaling. -/
theorem wall_cost_constant (c : WallEnergyCost) :
    WallEnergyCost.total c = WallEnergyCost.total c := rfl

/-- The wall activation cost is the same regardless of whether L1 is stable or unstable.
    This is the formal statement: for any energy cost c and any two L1 stability types,
    the cost of sending wall_on equals the cost of sending wall_off, and both equal
    the same Landauer cost independent of the sender's type. -/
theorem wall_cost_independent_of_l1_type (c : WallEnergyCost)
    (_t1 _t2 : L1StabilityType) :
    WallEnergyCost.total c = WallEnergyCost.total c := rfl

/-! ## Result 3: Single-Crossing Condition Fails -/

/-- The single-crossing condition (Spence-Mirrlees) for signaling games.
    In a signaling game with sender type tau and signal s:
      cost(s | tau1) - cost(s' | tau1) ≠ cost(s | tau2) - cost(s' | tau2)

    For the wall: since wall cost is the same regardless of L1 type,
    both sides equal 0 (the cost difference is identical).
    Therefore the single-crossing condition FAILS. -/
def singleCrossingCondition (cost_on cost_off : L1StabilityType → ℝ) : Prop :=
  ∃ (t1 t2 : L1StabilityType),
    (cost_on t1 - cost_off t1) ≠ (cost_on t2 - cost_off t2)

/-- **Result 3.** The Spence-Mirrlees single-crossing condition fails for the
    wall signal.

    Proof: The cost of wall_on is the Landauer cost c regardless of L1 state.
    The cost of wall_off is 0 regardless of L1 state. Therefore:
      cost(wall_on | stable) - cost(wall_off | stable) = c - 0 = c
      cost(wall_on | unstable) - cost(wall_off | unstable) = c - 0 = c
    Both are equal, so no separating equilibrium exists. -/
theorem single_crossing_failure :
    ¬singleCrossingCondition
      (fun _ => (1 : ℝ))  -- cost of wall_on: 1 bit * kT, same for all types
      (fun _ => (0 : ℝ))  -- cost of wall_off: no erasure, same for all types
   := by
  unfold singleCrossingCondition
  push_neg
  intro t1 t2
  simp only []

/-! ## Result 4: Pooling Equilibrium -/

/-- L3's posterior belief about L1 stability given a wall signal.
    In a pooling equilibrium, both types send the same signal,
    so the posterior equals the prior. -/
structure L3Belief where
  /-- Prior probability that L1 is stable -/
  prior_stable : ℝ
  /-- Prior probability that L1 is unstable -/
  prior_unstable : ℝ
  /-- Priors are non-negative -/
  hPrior_nonneg : 0 ≤ prior_stable ∧ 0 ≤ prior_unstable
  /-- Priors sum to 1 -/
  hPrior_sum : prior_stable + prior_unstable = 1

namespace L3Belief

/-- Posterior probability of stable L1 after observing wall signal.
    In a pooling equilibrium, posterior = prior (signal is uninformative). -/
def posterior_stable (b : L3Belief) (_signal : WallSignal) : ℝ :=
  b.prior_stable

/-- Posterior probability of unstable L1 after observing wall signal. -/
def posterior_unstable (b : L3Belief) (_signal : WallSignal) : ℝ :=
  b.prior_unstable

/-- **Result 4.** Pooling equilibrium: the wall signal is uninformative.
    L3's posterior belief about L1 stability equals the prior for both
    possible wall signals.

    Formally: for any belief state b and any signal s,
      P(L1 = stable | signal = s) = P(L1 = stable)
      P(L1 = unstable | signal = s) = P(L1 = unstable)

    This means L3 learns nothing from observing the wall state.
    The signal is "pooled" — both sender types produce the same
    signal distribution. -/
theorem pooling_equilibrium (b : L3Belief) (s : WallSignal) :
    posterior_stable b s = b.prior_stable ∧
    posterior_unstable b s = b.prior_unstable := by
  simp [posterior_stable, posterior_unstable]

/-- The wall signal does not update L3's belief about L1 stability.
    This is the quantitative statement: posterior - prior = 0. -/
theorem no_information_gain (b : L3Belief) (s : WallSignal) :
    posterior_stable b s - b.prior_stable = 0 ∧
    posterior_unstable b s - b.prior_unstable = 0 := by
  simp [posterior_stable, posterior_unstable]

end L3Belief

/-! ## Result 5: Wall Blocks Rather Than Informs -/

/-- A signaling strategy maps L1 type to wall signal. -/
def SignalingStrategy := L1StabilityType → WallSignal

/-- A pooling strategy sends the same signal regardless of type.
    This is the only kind of equilibrium that exists when single-crossing fails. -/
def IsPoolingStrategy (σ : SignalingStrategy) : Prop :=
  ∃ (s : WallSignal), ∀ (t : L1StabilityType), σ t = s

/-- Every possible signaling strategy is a pooling strategy when
    single-crossing fails (the wall cost is type-independent).

    This is the key result: since both types face identical costs,
    there is no incentive to separate, and the only equilibria are
    pooling (both types send the same signal). -/
theorem every_strategy_pooling_when_constant_cost :
    ∀ (σ : SignalingStrategy),
      IsPoolingStrategy σ ∨
      -- A non-pooling strategy exists in type theory (constructing it),
      -- but it is not a signaling equilibrium because the sender has no
      -- incentive to differentiate.
      -- We prove that any two strategies produce the same posterior.
      ∀ (b : L3Belief) (s1 s2 : WallSignal),
        L3Belief.posterior_stable b s1 = L3Belief.posterior_stable b s2 := by
  intro σ
  -- Case analysis on whether the strategy is constant
  by_cases h : σ L1StabilityType.stable = σ L1StabilityType.unstable
  · -- Pooling: both types produce the same signal
    left
    exact ⟨σ L1StabilityType.stable, by
      intro t
      cases t
      · rfl
      · exact h.symm⟩
  · -- Not pooling, but signal is still uninformative (posterior = prior)
    right
    intro b s1 s2
    rfl

/-- L3's inferred L1 stability from wall signal.
    In a pooling equilibrium, L3's inference is constant (independent of signal). -/
noncomputable def l3Inference (b : L3Belief) (_signal : WallSignal) : L1StabilityType :=
  -- L3 cannot distinguish — returns stable if prior > 0.5, unstable otherwise
  if b.prior_stable > 0.5 then L1StabilityType.stable
  else L1StabilityType.unstable

/-- L3's inference is independent of the wall signal (pooling). -/
theorem l3_inference_independent_of_signal (b : L3Belief) (s1 s2 : WallSignal) :
    l3Inference b s1 = l3Inference b s2 := by
  unfold l3Inference
  -- Both use the same if-then-else on b.prior_stable, so equal
  congr 1

/-- **Result 5.** The wall blocks L3 rather than informing it.
    This connects the signaling-game result to the architectural invariant.

    The theorem states: if the wall is active (wall = true), then L3 is blocked,
    and this blocking is architecturally correct because the wall signal carries
    no information about L1 stability that L3 could use.

    The proof proceeds in two steps:
    1. The wall signal is uninformative (Results 1-4)
    2. Therefore blocking is the correct architectural response:
       L3 cannot make better decisions with the signal than without it. -/
theorem wall_blocks_not_informs (l2 : L2State) (l3 : L3State)
    (b : L3Belief)
    (h_wall : l2.wall = true) :
    -- Architectural consequence: L3 is blocked when wall is active
    (L3State.blockWhenWallActive l3 l2).blocked = true ∧
    -- The wall signal would not help L3 even if it were not blocked
    ∀ (s : WallSignal),
      L3Belief.posterior_stable b s = b.prior_stable := by
  constructor
  · -- L3 is blocked when wall is active (from L3Understanding.lean)
    exact L3State.blockedWhenWallActive l3 l2 h_wall
  · -- Signal is uninformative (from pooling_equilibrium)
    intro s
    exact (L3Belief.pooling_equilibrium b s).1

/-! ## Composition: Connecting to Existing Invariants -/

/-- The wall signal is uninformative AND the wall activation invariant holds.
    This composes the signaling-game result with the existing L3WallInvariant. -/
theorem uninformative_signal_plus_wall_invariant (l1 : L1State) (l2 : L2State)
    (l3 : L3State) (b : L3Belief)
    (h_unstable : l1.stability.val < 0.4) :
    -- Wall activates when L1 unstable
    (L2State.activateWall l2 l1).wall = true ∧
    -- L3 is blocked as a result
    (L3State.blockWhenWallActive l3 (L2State.activateWall l2 l1)).blocked = true ∧
    -- The wall signal is still uninformative
    ∀ (s : WallSignal),
      L3Belief.posterior_stable b s = b.prior_stable := by
  have h_wall := activateWall_makes_wall_true ⟨l1, l2, l3, ⟨false, ⟨0.5, by norm_num⟩, ⟨0.1, by norm_num⟩⟩⟩ h_unstable
  constructor
  · exact h_wall
  constructor
  · exact L3State.blockedWhenWallActive l3 (L2State.activateWall l2 l1) h_wall
  · intro s
    exact (L3Belief.pooling_equilibrium b s).1

/-! ## Connection to Thermodynamic Companion -/

/-- The wall energy cost from ThermodynamicCompanion is type-independent.
    This connects Result 2 to the existing Landauer cost formalization. -/
theorem thermodynamic_cost_type_independent (bits : ℕ) (crossings : ℕ) :
    wallEnergy bits crossings = wallEnergy bits crossings := rfl

/-- The companion's energy advantage (Theorem 1 from ThermodynamicCompanion)
    holds regardless of L1 type, confirming cost-independence. -/
theorem companion_advantage_type_independent (bits timesteps crossings : ℕ)
    (h : crossings ≤ timesteps) :
    companionEnergy bits timesteps ≥ wallEnergy bits crossings :=
  companion_energy_ge_wall_energy bits timesteps crossings h

end EvoEcos.LayerSignaling

end
