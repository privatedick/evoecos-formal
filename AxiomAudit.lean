/-
Axiom audit — the machine-checked backing for this repo's "0 sorry" claim.
=========================================================================

`lake build` alone does NOT establish "0 sorry": Lean emits `declaration uses
'sorry'` as a *warning* and still exits 0. A line-anchored `grep '^\s*sorry'`
does not establish it either — it misses `exact sorry`, `:= sorry`, and
`<;> sorry`.

This module closes both gaps. It walks every declaration that this repository's
own modules contribute to the environment, collects the axioms each one
transitively depends on, and fails elaboration — and therefore `lake build` —
if any axiom outside Lean's three standard ones shows up.

  * `sorry` anywhere, in any syntactic position, surfaces as `sorryAx`;
  * an `axiom` command added to this repo surfaces under its own name.

It is self-maintaining: a theorem added tomorrow is audited without anyone
remembering to list it here.

What it deliberately does NOT claim: the three axioms below are permitted, since
they are Lean's standard classical foundation and essentially all of Mathlib
depends on them. "0 axiom" here means "no repo-declared axiom and no `sorryAx`",
not "no axioms at all".
-/

import Architecture
import EvoEcos
import InfoTheory
import Kernel
import ProvablyCorrectControllers
import Thresholds
import Lean

open Lean

namespace AxiomAudit

/-- Lean's three standard axioms. Anything else in a repo declaration's axiom
footprint is a build failure. -/
def allowedAxioms : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]

/-- Roots of the libraries this repository contributes, as opposed to Mathlib
and friends. Every `lean_lib` in `lakefile.lean` must appear here, or its
theorems are silently exempt from the audit. -/
def repoRoots : Array Name :=
  #[`Architecture, `EvoEcos, `InfoTheory,
    `Kernel, `ProvablyCorrectControllers, `Thresholds]

/-- Is this module contributed by this repository? -/
def isRepoModule (m : Name) : Bool :=
  repoRoots.any fun r => m == r || r.isPrefixOf m

/-- Every repo declaration whose axiom footprint escapes `allowedAxioms`. -/
def offenders (env : Environment) : Array (Name × Array Name) := Id.run do
  let hdr := env.header
  let mut out : Array (Name × Array Name) := #[]
  for (modName, modData) in hdr.moduleNames.zip hdr.moduleData do
    if isRepoModule modName then
      for c in modData.constNames do
        let axs := ((CollectAxioms.collect c).run env).run {} |>.2 |>.axioms
        let bad := axs.filter (!allowedAxioms.contains ·)
        if !bad.isEmpty then
          out := out.push (c, bad)
  return out

end AxiomAudit

open AxiomAudit in
run_cmd do
  let env ← Lean.getEnv
  let bad := offenders env
  unless bad.isEmpty do
    let details := bad.map fun (c, axs) =>
      m!"  {c} depends on: {axs.toList}"
    Lean.throwError m!"axiom audit failed — \
      {bad.size} declaration(s) depend on axioms outside \
      [propext, Classical.choice, Quot.sound]:\n\
      {MessageData.joinSep details.toList "\n"}\n\n\
      A `sorryAx` here means a `sorry` reached the build. \
      The baseline for this repository is 0."
