# EvoEcos.Formal

Machine-checked invariants for layered agent architectures — the kind where a
supervisory layer gates a planning layer on a safety signal.

Lean 4 + Mathlib. **1,227 theorem/lemma declarations across 117 files, 0 `sorry`,
and no axiom outside Lean's standard three** — enforced by the build, not claimed
in prose.

## Why this exists

Runtime shields for agents currently split into two camps that don't meet. The
shielded-RL line has real theory but targets MDPs, not LLM agents. The
LLM-agent line has deployment, but its "verification" is usually a policy DSL
checked by another model — no mechanized proof anywhere.

This is the proof side of that seam: invariants stated and discharged in a
kernel-checked system, so a shield's guarantee is something you can verify
rather than something you take on trust.

## What's proved

The core is a three-layer architecture (operational / modelling / planning) and
the gate between them:

| Property | Statement |
|---|---|
| No collapse | operational stability stays positive |
| Wall invariant | stability below threshold ⟹ the gate is active |
| Blocked when walled | gate active ⟹ the planning layer cannot act |
| Independence | the operational layer runs without the planning layer |
| Bounded uncertainty | the modelling layer's uncertainty stays in [0,1] |
| Liveness | the gate cannot stall progress indefinitely |

The last one matters as much as the safety properties. A shield that can block
forever is not a shield anyone leaves switched on, so bounded-time advance is
proved rather than assumed.

Alongside these: information-theoretic bounds on what a gated layer can act on,
threshold results, and adaptive-companion and meta-learning theorems.

## The axiom gate

`0 sorry` is easy to claim and easy to get wrong — a line-anchored grep for
`sorry` misses `exact sorry`, which sits on a line starting with `exact`. So
the check here is not a grep. The build walks every declaration this repository
contributes and fails if any depends on an axiom outside Lean's standard three
(`propext`, `Classical.choice`, `Quot.sound`). That catches `sorryAx` in any
syntactic position, and any `axiom` command added later.

The gate has been tested adversarially rather than trusted: injecting
`exact sorry` into a proof makes the build fail with
`audit_canary_should_fail depends on: [sorryAx]`. That is the position a
line-anchored grep misses.

Two honest limits. First, 0 `sorry` means nothing is left unproved; it does not
mean every theorem is deep — judge the statements, not the count. Second, this
library is deliberately narrower than the research repository it came from. Two
blocks were cut while preparing it, for the same two reasons each: a DeFi
mechanism-design library that no longer compiled (it had never been in the
default target set, so nothing was building it), and a set of smart-contract
witness proofs that used `native_decide` — which discharges goals by running
compiled code instead of reducing in the kernel, and so introduces an axiom the
kernel never checks. Both were off-topic for layered agent architectures, and
both would have made the claim above false.

## Build

```bash
lake exe cache get   # prebuilt Mathlib — skip this and you compile it yourself
lake build
```

Pinned to Lean 4.29.1 and Mathlib v4.29.1 via `lean-toolchain` and
`lake-manifest.json`. A clean build emitting no `declaration uses 'sorry'`
warning is the real check.

## Using it

```lean
require evoecos from git
  "https://github.com/privatedick/evoecos-formal.git"
```

Apache 2.0 — use it, build on it, ship products with it. If you do, an issue
saying what you needed is more useful to me than a star.

## Status

Extracted from a larger private research repository, which is where the
empirical side lives: the same gate wired to a live model actuator, and a
30-seed control experiment finding that gating an LLM does **not** beat the
plain reflex controller it sits on top of (47.8 vs 46.4, Wilcoxon p=0.83). The
proofs say the gate blocks what it claims to block. They do not say blocking
earns its place — that is an open empirical question, and the negative result
is the current best evidence on it.
