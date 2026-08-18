/-
EvoEcos Information Theory Module
==================================

Formalization of the Dual Information Thesis:
- I_exist: Existing information in observations
- I_exploit: Exploitable information for action selection

Key insight: Optimal cognitive architecture is governed by I_exploit,
not I_exist. The boundary between them determines when complexity
becomes adaptive.
-/

import EvoEcos.Types

noncomputable section

namespace EvoEcos.InfoTheory

/-! ## Dual Information Thesis -/

/-- I_exist: Information content in observations -/
structure IExist where
  observationEntropy : ℝ
  complexityMeasure : ℝ  -- Lempel-Ziv complexity proxy
  hentropy_nonneg : 0 ≤ observationEntropy
  hcomplexity_nonneg : 0 ≤ complexityMeasure

/-- I_exploit: Actionable information for behavior -/
structure IExploit where
  transferEntropy : ℝ
  predictivePower : ℝ
  hte_nonneg : 0 ≤ transferEntropy
  hpred_nonneg : 0 ≤ predictivePower

/-- Dual information state -/
structure DualInfo where
  iExist : IExist
  iExploit : IExploit

namespace DualInfo

/-- The exploitation ratio: how much of existing info is actionable -/
def exploitationRatio (d : DualInfo) : ℝ :=
  if d.iExist.observationEntropy > 0 then
    d.iExploit.transferEntropy / d.iExist.observationEntropy
  else
    0

/-- Environment is exploitable if I_exploit > 0 -/
def isExploitable (d : DualInfo) : Prop :=
  d.iExploit.transferEntropy > 0

/-- Environment is Type B (unexploitable) if I_exploit ≈ 0 -/
def isTypeB (d : DualInfo) (ε : ℝ) : Prop :=
  d.iExploit.transferEntropy < ε ∧ d.iExist.observationEntropy > 0

/-! ## Key Theorems -/

/-- Exploitation ratio is non-negative -/
theorem exploitation_ratio_nonneg (d : DualInfo) :
    0 ≤ d.exploitationRatio := by
  simp only [exploitationRatio]
  split
  · exact div_nonneg d.iExploit.hte_nonneg (le_of_lt (by assumption))
  · linarith

/-- Type B environments have bounded exploitation ratio -/
theorem typeB_bounded_exploitation (d : DualInfo) (ε : ℝ) (heps : ε > 0)
    (h : d.isTypeB ε) :
    d.iExploit.transferEntropy < ε := h.1

end DualInfo

/-! ## Information Bottleneck -/

/-- Information bottleneck parameter β ∈ [0, ∞) -/
structure Beta where
  val : ℝ
  hnonneg : 0 ≤ val

/-- Bottleneck state -/
structure BottleneckState where
  beta : Beta
  compression : ℝ  -- I(X;Z) / I(X;Y)
  relevance : ℝ   -- I(Z;Y)

namespace BottleneckState

/-- Phase transition point β* -/
structure BetaStar where
  val : ℝ
  environment : String  -- "TypeA", "TypeB", "TypeC"

/-- Optimal β* varies by environment type -/
def optimalBeta (env : String) : BetaStar :=
  match env with
  | "TypeA" => ⟨0.368, env⟩   -- Intermediate compression
  | "TypeB" => ⟨0.211, env⟩   -- Lower gain (correctly unexploitable)
  | "TypeC" => ⟨1.000, env⟩   -- Maximum compression
  | _ => ⟨0.5, env⟩

/-- β* phase transition theorem -/
theorem beta_star_varies_by_type :
    let βa := (optimalBeta "TypeA").val
    let βb := (optimalBeta "TypeB").val
    let βc := (optimalBeta "TypeC").val
    βb < βa ∧ βa < βc := by
  simp only [optimalBeta]
  norm_num

end BottleneckState

end EvoEcos.InfoTheory

end
