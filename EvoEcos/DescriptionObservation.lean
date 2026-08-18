/-
Vulnerability Description as Non-Injective Projection
======================================================

A vulnerability's title/description is a non-injective projection of the
full vulnerability. Multiple vulnerabilities (different root causes,
different exploit paths, different severity) share the same surface
description. By ACD, there exist vulnerability predicates not verifiable
from descriptions alone.

Connection to the adversarial CVE test:
  The CVE classification experiment (2/5 correct on stratum 3) demonstrated
  that classifying vulnerabilities from titles fails because the
  title-to-mental-model projection is lossy. This file formalises that
  observation: descriptionObs discards root cause, exploit path, severity,
  and affected component. Any predicate depending on those hidden fields
  is counterfactual w.r.t. the description observation.

Results (0 sorry):
  1. description_obs_noninjective — description observation is non-injective
  2. classification_counterfactual_exists — ∃ unverifiable vulnerability predicates
  3. severity_recovery_counterfactual — severity assessment is counterfactual
  4. root_cause_counterfactual — root-cause identification is counterfactual
-/

import EvoEcos.ACD

namespace EvoEcos

open ObservationalSetup

/-! ## Abstract Types for Vulnerability Analysis -/

/-- What a title/description captures — only the surface-level summary. -/
abbrev Description := String

/-- A vulnerability with full context:
  (surface_description, root_cause, severity_score, exploit_path, affected_component).
  The description observation discards everything except the first field. -/
abbrev Vulnerability := String × String × Nat × String × String

/-! ## The Observation Function -/

/-- Description observation: projects a full vulnerability to its surface
description. Discards root cause, severity, exploit path, and affected
component. This is what a title-based classifier or a model reading CVE
summaries can see. -/
def descriptionObs (v : Vulnerability) : Description := v.1

/-! ## Non-Injectivity -/

/-- Description observation is non-injective: the same surface description
covers vulnerabilities with different root causes, severities, and exploit
paths. Two vulnerabilities sharing a title but differing in root cause
and severity witness the non-injectivity. -/
theorem description_obs_noninjective : ¬ Function.Injective descriptionObs := by
  intro h
  have h1 := @h ("buffer overflow in parser", "null deref", 7, "remote TCP", "libparse") ("buffer overflow in parser", "heap corruption", 9, "local priv esc", "libparse") rfl
  exact absurd (congrArg (fun v => v.2.2.1) h1) (by decide)

/-! ## ACD Applied to Vulnerability Classification -/

/-- The observational setup for vulnerability classification:
worlds are full vulnerabilities, observations are surface descriptions. -/
def vulnClassificationSetup (truth : Vulnerability → Bool) :
    ObservationalSetup Vulnerability Description where
  obs := descriptionObs
  truth := truth

/-- By ACD, non-injective description observation guarantees the existence
of vulnerability predicates not verifiable from descriptions alone. -/
theorem classification_counterfactual_exists :
    ∃ (truth : Vulnerability → Bool),
      ¬ ∀ w1 w2, descriptionObs w1 = descriptionObs w2 → truth w1 = truth w2 := by
  have h := description_obs_noninjective
  rw [Function.Injective] at h
  push_neg at h
  obtain ⟨a, b, h_obs, h_ne⟩ := h
  classical
  refine ⟨fun w => if w = a then true else false, ?_⟩
  intro hArch
  have h1 := hArch a b h_obs
  simp only [ite_true, ite_false, h_ne.symm] at h1
  nomatch h1

/-! ## Specific Counterfactual Witnesses -/

/-- Severity predicate: does the vulnerability have severity ≥ threshold?
Counterfactual because same description can have different severities. -/
def severityPredicate (threshold : Nat) (v : Vulnerability) : Bool :=
  if v.2.2.1 ≥ threshold then true else false

/-- Severity assessment from descriptions is counterfactual: two
vulnerabilities with the same surface description but different severity
scores witness the information loss. -/
theorem severity_recovery_counterfactual :
    (vulnClassificationSetup (severityPredicate 8)).Counterfactual := by
  refine ⟨("buffer overflow in parser", "null deref", 7, "remote TCP", "libparse"),
          ("buffer overflow in parser", "heap corruption", 9, "local priv esc", "libparse"),
          rfl, ?_⟩
  decide

/-- Root-cause predicate: does the vulnerability's root cause match
a target string? Counterfactual because same description can have
different root causes. -/
def rootCausePredicate (target : String) (v : Vulnerability) : Bool :=
  v.2.1 == target

/-- Root-cause identification from descriptions is counterfactual: two
vulnerabilities with the same surface description but different root
causes cannot be distinguished by description alone. -/
theorem root_cause_counterfactual :
    (vulnClassificationSetup (rootCausePredicate "null deref")).Counterfactual := by
  refine ⟨("buffer overflow in parser", "null deref", 7, "remote TCP", "libparse"),
          ("buffer overflow in parser", "heap corruption", 9, "local priv esc", "libparse"),
          rfl, ?_⟩
  decide

end EvoEcos
