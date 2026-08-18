import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Holding vs Identification: Scrutiny Monotonicity (empath domain)

**Date:** 2026-07-07

Formal companion to `experiment_holding_vs_identification_ess.py`
(decisions.md: `holding_vs_identification_ess` [CONFIRMED]). Proves the
three load-bearing monotonicity facts behind the sequential-elimination
finding: as extramural scrutiny `s` rises,

1. every leak payoff strictly falls,
2. holding's payoff strictly rises, and
3. a sneakier leak's advantage over an obvious leak strictly grows.

Together these imply leaks are eliminated in order of detectability
(facade → merger → hold restored) — the novel refinement beyond the
single-leak `liability_commitment_ess`.

## Relation to existing results

* `evolutionary_commitment_ess` + `liability_commitment_ess` prove the
  binary-gate-is-ESS / graded-is-invdaded results. This file does NOT
  re-derive those (re-skinning them would be epistemic dilution). It adds
  the ONE structural fact those namespaces could not state: when there are
  two leaks with different detectability, the sneakier one's advantage over
  the obvious one grows with scrutiny. `liability_commitment_ess` had a
  single leak (theater); the empath domain has two (identify = merger,
  theater = facade), so the inter-leak comparison is genuinely new.
* `malignant_leak`: "identify" IS the leak — surface-ok because genuinely
  felt, status-quo-preserving because non-generative. Theorem 3 is the
  formal face of "merger is sneakier than facade": both are leaks, but
  merger's lower exposure makes its payoff decay slower under scrutiny.

## Payoff model (per the experiment's DESIGN NOTE 4)

Under scrutiny `s`, with loop-closure value `V` (hold only), leak exposure
`X` (detectability), and scrutiny penalty `P`:

  payoff_holding(s) = D_h + s*V - C_h          -- exposure_h = 0
  payoff_leak(s)    = D_L - C_L - s * X_L * P  -- no loop-closure term

Hypotheses: `0 < V`, `0 < X_L`, `0 < P`. Slopes are constant in `s`.

## What this file proves (0 sorry)

* `leak_payoff_decreases_with_scrutiny` — leak payoff slope `-X*P < 0`.
* `hold_payoff_increases_with_scrutiny` — holding payoff slope `+V > 0`.
* `sneakier_leak_advantage_grows_with_scrutiny` — the snearky-vs-obvious
  advantage slope `P*(X_obvious - X_sneaky) > 0` (the novel theorem).
-/

namespace EvoEcos.HoldingIdentification

/-! ## Leak payoffs fall with scrutiny -/

/--
A leak strategy's payoff `D_L - C_L - s*X_L*P` is strictly decreasing in
scrutiny `s`: each unit of scrutiny exposes more of the facade/merger.
Slope = `-X_L*P < 0`. Applies to both `theater` (facade) and `identify`
(merger): any strategy that displays empathy without delivering loop-closure
loses payoff as observers gain the ability to distinguish performance from
transformation.
-/
theorem leak_payoff_decreases_with_scrutiny
    (D_L C_L X_L penalty : ℝ) (s1 s2 : ℝ)
    (hX : 0 < X_L) (hP : 0 < penalty) (hs : s1 < s2) :
    D_L - C_L - s2 * X_L * penalty < D_L - C_L - s1 * X_L * penalty := by
  have eq :
      (D_L - C_L - s1 * X_L * penalty) - (D_L - C_L - s2 * X_L * penalty)
        = (s2 - s1) * X_L * penalty := by ring
  have pos : 0 < (s2 - s1) * X_L * penalty :=
    mul_pos (mul_pos (sub_pos.mpr hs) hX) hP
  linarith

/-! ## Hold payoff rises with scrutiny -/

/--
Holding's payoff `D_h - C_h + s*V` is strictly increasing in scrutiny `s`:
scrutiny reveals loop-closure, which only holding delivers. Slope = `+V > 0`.
(`exposure_h = 0`: holding has nothing to expose — it is the only strategy
whose payoff is unpenalised by scrutiny and rewarded by it.)
-/
theorem hold_payoff_increases_with_scrutiny
    (D_h C_h V : ℝ) (s1 s2 : ℝ)
    (hV : 0 < V) (hs : s1 < s2) :
    D_h - C_h + s1 * V < D_h - C_h + s2 * V := by
  have eq : (D_h - C_h + s2 * V) - (D_h - C_h + s1 * V) = (s2 - s1) * V := by ring
  have pos : 0 < (s2 - s1) * V := mul_pos (sub_pos.mpr hs) hV
  linarith

/-! ## The sneakier leak's advantage grows with scrutiny (novel theorem) -/

/--
For two leak strategies `L_obvious` (exposure `X1`) and `L_sneaky` (exposure
`X2`) with `X2 < X1` (the obvious leak is more detectable), the sneaky leak's
payoff advantage over the obvious one strictly grows with scrutiny `s`.
The advantage's slope in `s` is `penalty * (X1 - X2) > 0`.

This is the structural fact behind "merger is sneakier than facade": both
are leaks (zero loop-closure), but merger (`X2`) is genuinely felt and thus
harder to detect than pure facade (`X1`). Under increasing scrutiny the
facade is eliminated first; the merger survives until higher scrutiny. The
empath domain's two-leak sequential elimination (H3 in the experiment) is
this theorem's empirical shadow — and it is the claim `liability_commitment_ess`
could not state, since that setup had a single leak.
-/
theorem sneakier_leak_advantage_grows_with_scrutiny
    (D1 C1 X1 D2 C2 X2 penalty : ℝ) (s1 s2 : ℝ)
    (hX : X2 < X1) (hP : 0 < penalty) (hs : s1 < s2) :
    (D2 - C2 - s2 * X2 * penalty) - (D1 - C1 - s2 * X1 * penalty)
      > (D2 - C2 - s1 * X2 * penalty) - (D1 - C1 - s1 * X1 * penalty) := by
  have eq :
      ((D2 - C2 - s2 * X2 * penalty) - (D1 - C1 - s2 * X1 * penalty))
        - ((D2 - C2 - s1 * X2 * penalty) - (D1 - C1 - s1 * X1 * penalty))
        = (s2 - s1) * penalty * (X1 - X2) := by ring
  have pos : 0 < (s2 - s1) * penalty * (X1 - X2) :=
    mul_pos (mul_pos (sub_pos.mpr hs) hP) (sub_pos.mpr hX)
  linarith

end EvoEcos.HoldingIdentification
