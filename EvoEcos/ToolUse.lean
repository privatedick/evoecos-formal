/-
Tool Use — when is introducing a tool worth its cost?
=====================================================

A tool `T` transforms information and capability: a calculator, compiler, debugger,
search engine, LLM, microscope, notebook. This module formalises the criterion for
when using `T` is worth it, as one inequality over a value/cost decomposition.

The naive criterion sums four "value" terms — information gain `ΔI`, decision value
`ΔU`, compute savings `ΔK`, action-capability `ΔA` — against five cost terms
(discover, learn, execute, maintain, verify). That double-counts: `ΔI` is measured
in *bits*, the others in *utility*, and the value of the information is already
realised *through* the decisions it changes (Value of Information = expected
utility gained from acting on the reduced uncertainty). This module encodes the
corrected criterion: `value = ΔU + ΔK + ΔA` (utility only), with `ΔI` the
*mechanism* by which a tool raises `ΔU`, not a separate additive term. Reliability
(Model 8 in the source MAP) is integrated as a risk adjustment on value, not a
parallel model.

HONESTY BOUND: the value and cost components are *modelling parameters* over `ℝ`
(the same epistemic status as `DecisionCost.openness`) — no calibrated unit of
"information" or "effort" is instantiated here. The content is the *structure* of
the criterion (additive decomposition, the VoI correction, reliability integration,
composition/removability), not a measurement instrument.

Composes with the loop-closure criterion: the metabolism-skill decision "is wiring
this finding into the runtime worth its cost?" (guards: live-path, invariant,
modelling-fit, lockout — `/metabolize`) is the runtime instance of `justified`
below, with the guards as the verify/maintain cost checks. Connects to
`InfoTheoreticWall` (ΔI bounded-but-loose): the wall's information gain is the
mechanism term whose decision-value (`ΔU`) the criterion weighs against cost.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

noncomputable section

namespace EvoEcos.ToolUse

/-- Gross value produced by a tool, in utility units: decisions changed (`ΔU`),
computation saved (`ΔK`), action capability gained (`ΔA`). Information gain (`ΔI`)
is deliberately *not* a term — its value is realised through `ΔU` (Value of
Information), so summing it alongside `ΔU` double-counts across incommensurable
units (bits vs utils). -/
def value (ΔU ΔK ΔA : ℝ) : ℝ := ΔU + ΔK + ΔA

/-- Total cost of using a tool: discover, learn, execute, maintain, verify. The
hidden terms (`cMaintain`, `cVerify`) are where tool-use decisions typically
fail — they are underestimated because they are not part of "running" the tool. -/
def totalCost (cDiscover cLearn cExecute cMaintain cVerify : ℝ) : ℝ :=
  cDiscover + cLearn + cExecute + cMaintain + cVerify

/-- Realised (risk-adjusted) value: `pCorrect · V − pError · loss`, where `loss`
is the utility forfeited by acting on a wrong tool output. Reliability modulates
value rather than being a separate model — a hallucinating tool claims high `V`
but delivers low realised value. -/
def realised (V pCorrect pError loss : ℝ) : ℝ := pCorrect * V - pError * loss

/-- Net benefit of a tool: realised value minus total cost. -/
def net (V cost pCorrect pError loss : ℝ) : ℝ :=
  realised V pCorrect pError loss - cost

/-- A tool is justified iff its net benefit is positive. -/
def justified (V cost pCorrect pError loss : ℝ) : Prop :=
  net V cost pCorrect pError loss > 0

/-- **Value of Information principle.** A tool that changes no decision, saves no
computation, and adds no action capability has zero value — *regardless of how
much information it appears to carry*. Information has value only through the
decisions / compute / actions it changes. This is why `value` has no `ΔI` term. -/
theorem value_zero_if_no_gains {ΔU ΔK ΔA : ℝ}
    (hU : ΔU = 0) (hK : ΔK = 0) (hA : ΔA = 0) :
    value ΔU ΔK ΔA = 0 := by
  simp [value, hU, hK, hA]

/-- Information that changes no decision contributes nothing to value: holding
`ΔK`, `ΔA` fixed, a tool with `ΔU = 0` is worth no more than one that carries no
information at all. -/
theorem info_without_decision_contributes_nothing {ΔU ΔK ΔA : ℝ}
    (hU : ΔU = 0) : value ΔU ΔK ΔA = value 0 ΔK ΔA := by
  simp [value, hU]

/-- **Reliability bound.** A sufficiently error-prone tool has non-positive
realised value even with arbitrarily large gross value `V` — when
`pError · loss ≥ pCorrect · V`, the expected loss from wrong outputs dominates the
expected benefit. Reliability is therefore not a parallel model but a modifier
that can zero (or negate) gross value. -/
theorem error_can_negate_value (V pCorrect pError loss : ℝ)
    (h : pCorrect * V ≤ pError * loss) :
    realised V pCorrect pError loss ≤ 0 := by
  unfold realised; linarith

/-- **Justification unfolds to the corrected inequality.** A tool is justified
iff `pCorrect · V − pError · loss > cost`, with `V = ΔU + ΔK + ΔA`. -/
theorem justified_iff (V cost pCorrect pError loss : ℝ) :
    justified V cost pCorrect pError loss ↔
      pCorrect * V - pError * loss - cost > 0 := by
  rfl

/-- With non-negative costs, justification implies realised value exceeds every
individual cost component — in particular the often-hidden `cVerify`. The verify
cost is bounded above by the realised value, which is why high-error tools (large
`cVerify`) are hard to justify. -/
theorem justified_beats_verify_cost
    (V cDiscover cLearn cExecute cMaintain cVerify pCorrect pError loss : ℝ)
    (hN : 0 ≤ cDiscover) (hL : 0 ≤ cLearn) (hE : 0 ≤ cExecute)
    (hM : 0 ≤ cMaintain)
    (hj : justified V (totalCost cDiscover cLearn cExecute cMaintain cVerify)
                       pCorrect pError loss) :
    realised V pCorrect pError loss > cVerify := by
  unfold justified net at hj
  have hcost : totalCost cDiscover cLearn cExecute cMaintain cVerify ≥ cVerify := by
    unfold totalCost; linarith
  linarith

/-- **Composition split.** The net benefit of a two-stage composition
(`V₁ + V₂`, summed cost) decomposes into the first stage's net plus the second
stage's reliability-weighted contribution. The error `loss` is counted once at the
composition level, not double-counted per stage. -/
theorem net_composition_split (V₁ V₂ C₁ C₂ pCorrect pError loss : ℝ) :
    net (V₁ + V₂) (C₁ + C₂) pCorrect pError loss =
      net V₁ C₁ pCorrect pError loss + (pCorrect * V₂ - C₂) := by
  unfold net realised; ring

/-- **Removability.** A stage whose reliability-weighted contribution is
non-positive (`pCorrect · V₂ ≤ C₂`) is removable: dropping it does not decrease
the total net benefit. This is the formal version of "each stage in a tool chain
must increase value or reduce cost, otherwise remove it." -/
theorem stage_removable_if_nonpositive (V₁ V₂ C₁ C₂ pCorrect pError loss : ℝ)
    (h : pCorrect * V₂ - C₂ ≤ 0) :
    net (V₁ + V₂) (C₁ + C₂) pCorrect pError loss ≤
      net V₁ C₁ pCorrect pError loss := by
  rw [net_composition_split]; linarith

end EvoEcos.ToolUse
