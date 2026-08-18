/-
Tool-Use Ecosystem — the publisher as a quality signal
=======================================================

Extends `ToolUse` from one tool to a *family* under a consistent tool philosophy
(narrow scope, high precision, no feature creep, evidence-driven). The individual
criterion `V(T) > cost` becomes superadditive over a family:

    familyValue = Σ V(T_i) + V_ecosystem

The key correction (vs. treating `V_ecosystem` as a lump): the ecosystem value is
*aggregate evaluation-cost-saved*. A trusted publisher shrinks each tool's
`C(discover) + C(learn) + C(verify)` — the exact cost terms from `ToolUse`. So
`V_ecosystem = Σ_i τ·(cDiscover_i + cLearn_i + cVerify_i)`, where `τ ∈ [0,1]` is
the publisher-trust capital accumulated by the track record. This is the formal
hook back into the single-tool criterion: trust raises each tool's net by lowering
its evaluation-cost terms, and the saving compounds across tools because the trust
is shared.

The information-theoretic reading — `I(Publisher; ToolQuality) > 0`, a meta-signal
that reduces the user's uncertainty *before* a tool runs — is the *interpretation*
of `τ` (a prior-shifting channel). This module formalises the COST mechanism (the
provable part); the full mutual-information statement would require probability
machinery not instantiated here (HONESTY BOUND, cf. `ToolUse`, `info_theory_wall_limits`).

The load-bearing formal content is the *asymmetric fragility*: trust is a shared
commons across the family, so one mediocre tool (a `τ`-reducing breach) lowers the
net benefit of *every* tool, not just itself — and the family-net loss can exceed
the bad tool's own value. "Explicitly refuses feature creep" is therefore tail-risk
management, not preference: one prior-destroying release pollutes the commons for
all future releases, because the trust term is shared.

HONESTY BOUND: `τ` and the cost components are modelling parameters over `ℝ` (same
status as `ToolUse`'s value/cost terms). The 2-tool family below demonstrates every
mechanism; linearity generalises to `n` tools (each theorem's proof is `ring`).

Composes with `ToolUse` (per-tool value/cost decomposition). The metabolism
loop-closure criterion is the runtime instance; this is its multi-tool / reputation
extension.
-/

import EvoEcos.ToolUse
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

noncomputable section

namespace EvoEcos.ToolUseEcosystem

open EvoEcos.ToolUse (totalCost)

/-- Effective cost of a tool under publisher trust `τ`: the evaluation costs
(discover, learn, verify) are reduced by factor `(1 − τ)`; execute + maintain are
unaffected (trust does not run or maintain the tool for you). -/
def effectiveCost (cDiscover cLearn cExecute cMaintain cVerify τ : ℝ) : ℝ :=
  cExecute + cMaintain + (1 - τ) * (cDiscover + cLearn + cVerify)

/-- Net benefit of a single tool under publisher trust `τ`. -/
def netTrusted (V cDiscover cLearn cExecute cMaintain cVerify τ : ℝ) : ℝ :=
  V - effectiveCost cDiscover cLearn cExecute cMaintain cVerify τ

/-- Ecosystem bonus contributed by one tool: the evaluation cost its presence,
via shared trust, saves the user. -/
def ecosystemBonusOne (cDiscover cLearn cVerify τ : ℝ) : ℝ :=
  τ * (cDiscover + cLearn + cVerify)

/-- Ecosystem bonus over a 2-tool family. -/
def ecosystemBonusTwo (cD1 cL1 cV1 cD2 cL2 cV2 τ : ℝ) : ℝ :=
  ecosystemBonusOne cD1 cL1 cV1 τ + ecosystemBonusOne cD2 cL2 cV2 τ

/-- At `τ = 0` (no publisher trust) the trusted net reduces to the untrusted net
(`V − totalCost`): trust is purely additive on top of the single-tool criterion. -/
theorem netTrusted_eq_untrusted_at_zero_trust
    (V cD cL cE cM cV : ℝ) :
    netTrusted V cD cL cE cM cV 0 = V - totalCost cD cL cE cM cV := by
  unfold netTrusted effectiveCost totalCost; ring

/-- **Monotonicity in trust.** Higher publisher trust never lowers a tool's net
benefit — it only shrinks the evaluation-cost terms. (Requires evaluation costs
non-negative, the real-world case.) -/
theorem netTrusted_monotone_in_trust
    (V cD cL cE cM cV τ τ' : ℝ)
    (hτ : τ ≤ τ') (hD : 0 ≤ cD) (hL : 0 ≤ cL) (hV : 0 ≤ cV) :
    netTrusted V cD cL cE cM cV τ ≤ netTrusted V cD cL cE cM cV τ' := by
  unfold netTrusted effectiveCost
  have hs : 0 ≤ cD + cL + cV := by linarith
  have hkey : 0 ≤ (τ' - τ) * (cD + cL + cV) := mul_nonneg (by linarith) hs
  linarith

/-- **Superadditive decomposition.** The 2-tool family net (under shared trust)
equals the sum of the untrusted nets plus the ecosystem bonus. This is the formal
statement that family value is superadditive, with the bonus identified as
aggregate evaluation-cost-saved. -/
theorem familyNet_eq_sumUntrusted_plus_bonus
    (V1 V2 cD1 cL1 cE1 cM1 cV1 cD2 cL2 cE2 cM2 cV2 τ : ℝ) :
    netTrusted V1 cD1 cL1 cE1 cM1 cV1 τ + netTrusted V2 cD2 cL2 cE2 cM2 cV2 τ
    = (V1 - totalCost cD1 cL1 cE1 cM1 cV1) + (V2 - totalCost cD2 cL2 cE2 cM2 cV2)
      + ecosystemBonusTwo cD1 cL1 cV1 cD2 cL2 cV2 τ := by
  unfold netTrusted effectiveCost totalCost ecosystemBonusTwo ecosystemBonusOne
  ring

/-- **Superadditivity (weak).** With non-negative trust and evaluation costs, the
family net is at least the sum of untrusted nets. -/
theorem familyNet_superadditive
    (V1 V2 cD1 cL1 cE1 cM1 cV1 cD2 cL2 cE2 cM2 cV2 τ : ℝ)
    (hτ : 0 ≤ τ) (hD1 : 0 ≤ cD1) (hL1 : 0 ≤ cL1) (hV1 : 0 ≤ cV1)
    (hD2 : 0 ≤ cD2) (hL2 : 0 ≤ cL2) (hV2 : 0 ≤ cV2) :
    (V1 - totalCost cD1 cL1 cE1 cM1 cV1) + (V2 - totalCost cD2 cL2 cE2 cM2 cV2)
    ≤ netTrusted V1 cD1 cL1 cE1 cM1 cV1 τ + netTrusted V2 cD2 cL2 cE2 cM2 cV2 τ := by
  rw [familyNet_eq_sumUntrusted_plus_bonus]
  unfold ecosystemBonusTwo ecosystemBonusOne
  have : 0 ≤ τ * (cD1 + cL1 + cV1) + (τ * (cD2 + cL2 + cV2)) := by
    have s1 : 0 ≤ cD1 + cL1 + cV1 := by linarith
    have s2 : 0 ≤ cD2 + cL2 + cV2 := by linarith
    nlinarith
  linarith

/-- **Commons-pollution (fragility).** A trust breach (`τ` reduced to `τ' < τ`)
lowers the net benefit of an *innocent* tool — one that did nothing wrong. Because
trust is shared, a breach in tool 1's quality pollutes tool 2's net value. -/
theorem breach_reduces_innocent_tool
    (V2 cD2 cL2 cE2 cM2 cV2 τ τ' : ℝ)
    (hbreach : τ' ≤ τ) (hD2 : 0 ≤ cD2) (hL2 : 0 ≤ cL2) (hV2 : 0 ≤ cV2) :
    netTrusted V2 cD2 cL2 cE2 cM2 cV2 τ' ≤ netTrusted V2 cD2 cL2 cE2 cM2 cV2 τ :=
  netTrusted_monotone_in_trust V2 cD2 cL2 cE2 cM2 cV2 τ' τ hbreach hD2 hL2 hV2

/-- **Family-net breach loss.** Reducing trust from `τ` to `τ'` costs the family
exactly `(τ − τ')·(evalsum₁ + evalsum₂)` of net benefit — the entire shared bonus
shrinks. -/
theorem familyNet_breach_loss
    (V1 V2 cD1 cL1 cE1 cM1 cV1 cD2 cL2 cE2 cM2 cV2 τ τ' : ℝ) :
    (netTrusted V1 cD1 cL1 cE1 cM1 cV1 τ + netTrusted V2 cD2 cL2 cE2 cM2 cV2 τ)
    - (netTrusted V1 cD1 cL1 cE1 cM1 cV1 τ' + netTrusted V2 cD2 cL2 cE2 cM2 cV2 τ')
    = (τ - τ') * ((cD1 + cL1 + cV1) + (cD2 + cL2 + cV2)) := by
  unfold netTrusted effectiveCost; ring

/-- **Tail-risk.** A single breach's family-net loss can exceed a single tool's
gross value `V`: when `(τ − τ')·(evalsum₁ + evalsum₂) > V2`, the breach destroys
more value than tool 2 produces. One mediocre release can outweigh many good ones —
the convex downside that makes "refuse feature creep" load-bearing tail-risk
management rather than preference. -/
theorem breach_loss_can_exceed_single_tool_value
    (V1 V2 cD1 cL1 cE1 cM1 cV1 cD2 cL2 cE2 cM2 cV2 τ τ' : ℝ)
    (h : (τ - τ') * ((cD1 + cL1 + cV1) + (cD2 + cL2 + cV2)) > V2) :
    (netTrusted V1 cD1 cL1 cE1 cM1 cV1 τ + netTrusted V2 cD2 cL2 cE2 cM2 cV2 τ)
    - (netTrusted V1 cD1 cL1 cE1 cM1 cV1 τ' + netTrusted V2 cD2 cL2 cE2 cM2 cV2 τ')
    > V2 := by
  rw [familyNet_breach_loss]; exact h

end EvoEcos.ToolUseEcosystem
