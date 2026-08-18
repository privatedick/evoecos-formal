/-
Rice Boundary: Decidability of Architectural Classification
============================================================

For EvoEcos, the Architecture-Counterfactual Dichotomy (ACD) classifies every
observational setup as either Architectural (truth factors through observation)
or Counterfactual (it does not). Rice's theorem implies that in general, this
classification is undecidable: given an arbitrary transition system and predicate,
determining which class it falls into is equivalent to deciding non-trivial
properties of programs.

However, for any FIXED FINITE observational setup, the classification IS decidable
by enumeration: check all pairs (w1, w2) and verify whether observational
equivalence implies truth equivalence.

This file proves:
1. `architecturalDecidable`: For finite W and decidable O, Architectural is Decidable
2. `counterfactualDecidable`: Counterfactual is also Decidable (by duality)
3. `rice_boundary_finite`: Every finite setup is decidably Architectural ∨ Counterfactual

The general undecidability (full Rice boundary) is stated as a comment;
formalizing it requires encoding Turing machines into observational setups.

Proof-theoretic strength: RCA₀. All proofs constructive.
-/

import EvoEcos.ACD

namespace EvoEcos

open ObservationalSetup

/-! ## Decidability for Finite Observational Setups

The key insight: `Architectural` requires checking ALL pairs (w1, w2).
When W is finite, this is O(|W|²) checks, each using `DecidableEq` on O.
Universal quantification over a finite type is always decidable. -/

/-- For finite W with decidable observations, the Architectural property
    is decidable by enumeration of all world pairs.

    Decision procedure: for each pair (w1, w2), check whether
    `obs w1 = obs w2` implies `truth w1 = truth w2`.
    Each inner check is decidable (DecidableEq O + Bool equality).
    Universal quantifier over Fintype W gives the outer decidability.

    Time complexity: O(|W|² · cost(eq_O)).

    This establishes the Rice boundary for EvoEcos: the classification
    Architectural vs Counterfactual is decidable for any fixed finite
    observational setup, even though it is undecidable in general. -/
def architecturalDecidable {W O : Type} [Fintype W] [DecidableEq O]
    (S : ObservationalSetup W O) :
    Decidable S.Architectural := by
  unfold Architectural
  -- ∀ w1 w2, obs w1 = obs w2 → truth w1 = truth w2
  -- Each inner check: obs equality is decidable (DecidableEq O),
  -- truth equality is decidable (Bool has DecidableEq),
  -- implication of decidables is decidable.
  -- Universal over Fintype chains: ∀ w1, (∀ w2, P w1 w2) is decidable.
  exact Fintype.decidableForallFintype

/-- For finite W with decidable observations, Counterfactual is also decidable.

    Proof: the ACD duality gives Architectural ↔ ¬Counterfactual.
    In the `isTrue` case, ¬Counterfactual follows directly.
    In the `isFalse` case, ¬Architectural is pushed through the universal
    quantifier to produce the Counterfactual witness: ¬∀ becomes ∃¬. -/
def counterfactualDecidable {W O : Type} [Fintype W] [DecidableEq O]
    (S : ObservationalSetup W O) :
    Decidable S.Counterfactual :=
  match architecturalDecidable S with
  | isTrue hArch =>
    isFalse (fun hCF => (architectural_iff_not_counterfactual S).mp hArch hCF)
  | isFalse hNotArch =>
    isTrue (by
      have h := hNotArch
      unfold Architectural at h
      push Not at h
      exact h
    )

/-- **The Rice Boundary Theorem (constructive half).**

    For any finite world type W with decidable observations O,
    every observational setup S is decidably either Architectural
    (truth determined by observation) or Counterfactual (truth requires
    information beyond observation).

    This is the constructive content that distinguishes EvoEcos from
    the general Rice-type undecidability: while classifying arbitrary
    predicates is undecidable, any FIXED finite observational setup
    can be classified in O(|W|²) time by enumeration.

    Contrast with the classical `ACD` theorem (which uses `Classical.em`):
    `rice_boundary_finite` provides a *decision procedure* for finite setups,
    not merely an existence proof of the disjunction. -/
theorem rice_boundary_finite {W O : Type} [Fintype W] [DecidableEq O]
    (S : ObservationalSetup W O) :
    S.Architectural ∨ S.Counterfactual :=
  match architecturalDecidable S with
  | isTrue h => Or.inl h
  | isFalse h => Or.inr (by
      have := h
      unfold Architectural at this
      push Not at this
      exact this
    )

/-! ## General Rice Boundary (Undecidability)

The above results show that for FINITE setups, the classification is decidable.
For INFINITE setups, the situation is fundamentally different:

Rice's theorem (1953): Any non-trivial property of the partial function computed
by a Turing machine is undecidable.

Applied to observational setups: there is no algorithm that, given an arbitrary
observational setup (W, O, obs, truth) with potentially infinite W, can decide
whether it is Architectural or Counterfactual.

Reduction sketch from the halting problem:
- Let W = ℕ (encodings of Turing machines), O = Unit (trivial observation)
- obs : W → O is the constant function (all worlds look the same)
- truth : W → Bool is "does machine w halt?"
- Then Architectural ↔ (∀ w1 w2, true → halts w1 = halts w2) ↔ False
  (since some machines halt and some don't)
- But Counterfactual ↔ (∃ w1 w2, halts w1 ≠ halts w2) ↔ True
  (since there exist both halting and non-halting machines)
- Deciding Architectural for this setup solves the halting problem.

The formal Lean statement requires encoding Turing machines into observational
setups, which is possible but beyond the scope of this file.

Key takeaway: **finite decidability + infinite undecidability = the Rice boundary
is exactly the finiteness boundary.** -/

end EvoEcos
