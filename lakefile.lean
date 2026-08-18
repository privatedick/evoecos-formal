import Lake
open Lake DSL

package «evoecos»

@[default_target]
lean_lib «EvoEcos» where
  -- Add library configuration options here

lean_lib «InfoTheory» where

lean_lib «Thresholds» where

lean_lib «Architecture» where

lean_lib «ProvablyCorrectControllers» where


/-- Reasoning Kernel Specification (RKS) — the minimal invariant substrate
    for incremental state revision. -/
lean_lib «Kernel» where

/-- The "0 sorry / 0 repo-declared axiom" gate, as a build target rather than a
    CI-only grep. It imports every library above and fails elaboration if any
    repo declaration depends on an axiom outside Lean's standard three. Being a
    default target means plain `lake build` enforces it. -/
@[default_target]
lean_lib «AxiomAudit» where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.29.1"
