/-
EvoEcos Types Module
====================

Core datatypes for the Stable Epistemic Bootstrap architecture.
This module defines the fundamental types used across all Lean
specifications for the EvoEcos system.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace EvoEcos

/-! ## Basic Type Aliases -/

/-- Probability values in [0, 1] -/
def Probability := { p : ℝ // 0 ≤ p ∧ p ≤ 1 }

namespace Probability

instance : Coe Probability ℝ where
  coe p := p.val

noncomputable def zero : Probability := ⟨0, by norm_num⟩
noncomputable def one : Probability := ⟨1, by norm_num⟩

noncomputable def add (p q : Probability) : Probability :=
  ⟨min 1 (p.val + q.val), by
    constructor
    · exact le_min (by linarith [p.property.1]) (by linarith [p.property.1, q.property.1])
    · exact min_le_left _ _⟩

noncomputable def mul (p q : Probability) : Probability :=
  ⟨p.val * q.val, by
    constructor
    · exact mul_nonneg p.property.1 q.property.1
    · calc p.val * q.val ≤ 1 * 1 := by
            apply mul_le_mul p.property.2 q.property.2 q.property.1 (by linarith [p.property.1])
          _ = 1 := by ring⟩

noncomputable instance : Add Probability where add := add
noncomputable instance : Mul Probability where mul := mul

end Probability

/-! ## Action Type -/

/-- Types of actions the system can take -/
inductive ActionType where
  | none : ActionType      -- No action (blocked)
  | reflex : ActionType    -- Hard-wired response (no cognitive cost)
  | heuristic : ActionType -- Simple rule-based action (low cost)
  | planned : ActionType   -- Complex planned action (high cost)
deriving Repr, DecidableEq

/-- An action with safety and complexity scores -/
structure Action where
  type : ActionType
  safetyScore : Probability
  complexity : Probability

/-! ## Perception Type -/

/-- Perception from the environment -/
structure Perception where
  data : ℝ
  reliability : Probability
  threatLevel : Probability

/-! ## Hypothesis Type -/

/-- A Bayesian hypothesis about world state -/
structure Hypothesis where
  stateId : String
  prior : Probability
  posterior : Probability
  evidenceCount : Nat

/-! ## Resource Budget -/

/-- Available cognitive resources -/
structure ResourceBudget where
  energy : ℝ
  computation : ℝ
  memory : ℝ
  henergy_nonneg : 0 ≤ energy
  hcomput_nonneg : 0 ≤ computation
  hmemory_nonneg : 0 ≤ memory

namespace ResourceBudget

/-- Check if resources are sufficient for a cost -/
def canAfford (rb : ResourceBudget) (cost : ℝ) : Prop :=
  rb.energy ≥ cost ∧ rb.computation ≥ cost * 10

end ResourceBudget

/-! ## Layer Status Types -/

/-- L1 (Operational) Layer Status -/
structure L1Status where
  stabilityScore : Probability
  stressLevel : Probability
  active : Bool

/-- L2 (Modeling) Layer Status -/
structure L2Status where
  uncertaintyLevel : Probability
  active : Bool
  l3WallActive : Bool

/-- L3 (Understanding) Layer Status -/
structure L3Status where
  understandingDeveloped : Probability
  active : Bool
  blocked : Bool

/-! ## Bridge and Wall Types -/

/-- Communication channel between layers -/
structure Bridge where
  sourceLayer : Fin 3  -- 0 = L1, 1 = L2, 2 = L3
  targetLayer : Fin 3
  active : Bool
  currentInstruction : Action

/-- Wall protecting a layer from unwanted influence -/
structure Wall where
  protectedLayer : Fin 2  -- 0 = L1, 1 = L2
  active : Bool

/-! ## Helper Lemmas -/

namespace Probability

lemma val_nonneg (p : Probability) : 0 ≤ p.val := p.property.1
lemma val_le_one (p : Probability) : p.val ≤ 1 := p.property.2

lemma add_val (p q : Probability) :
    (p + q).val ≤ p.val + q.val := by
  show (add p q).val ≤ p.val + q.val
  simp only [add]
  exact min_le_right _ _

lemma mul_val (p q : Probability) :
    (p * q).val = p.val * q.val := rfl

end Probability

end EvoEcos
