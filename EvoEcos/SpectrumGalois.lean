import Mathlib

/-!
# Van Glabbeek's spectrum as a Galois connection (Layer 0)

Behavioural equivalences are the fixed points of an antitone Galois
connection ("polarity") between sets of tests, ordered by `⊆`, and
equivalences, ordered by refinement.

Layer 0: the polarity and its closure operator, Mathlib-only. CSLib
(bisimulation, simulation, trace equivalence, HML) enters at Layer 1+ and
is not required here. Independent of `ACDGalois.lean`'s observation-
vocabulary Galois construction.

The object is equivalences, not congruences: several spectrum equivalences
(e.g. trace equivalence for CCS choice) are not congruences; congruence is
a separate, operator-dependent layer, not treated here.

Parameterised by `(Proc, Ω)`: `Proc` is the process type, `Ω` the
observation type, a test is `Proc → Ω`. `Ω` is carried explicitly since the
closure-operator theorems mention only `E` and cannot recover `Ω` from it.

Results (0 sorry):
* `polarity` — `E` refines `induced Ω T` iff `T ⊆ respects Ω E`.
* `test_subset_respects_induced` — `T ⊆ respects Ω (induced Ω T)`.
* `cl_extensive`, `cl_monotone`, `cl_idempotent` — closure-operator laws for `cl Ω`.
* `induced_testable` — every induced equivalence is a fixed point of `cl Ω`.
* `spectrum_eq_closed_elements` — `Testable Ω E ↔ E ∈ range (induced Ω)`.
* `clHom` — `cl Ω` as a bundled monotone self-map.
* `closed_completeLattice` (Knaster–Tarski) — fixed points of `cl Ω` form a
  complete lattice: the van Glabbeek spectrum under refinement.
* `mem_closed_iff_testable` — fixed point ↔ `Testable Ω E`.

Not here: the named simulation-vs-failures antichain. The framework, the
trace/bisim points, and the generic antichain are in CSLib
(`Cslib.Foundations.Semantics.LTS.Spectrum.*`); the named antichain needs
failures semantics, which CSLib does not yet define.
-/

namespace Spectrum

variable {Proc : Type*}

/-- The equivalence a test class induces: agreement on every test in `T`.
    Antitone in `T` — more tests ⇒ finer (smaller) equivalence. -/
def induced (Ω : Type*) (T : Set (Proc → Ω)) (p q : Proc) : Prop :=
  ∀ t ∈ T, t p = t q

/-- The tests that respect an equivalence `E`: tests constant on every E-pair.
    Antitone in `E` — coarser `E` ⇒ fewer respecting tests. -/
def respects (Ω : Type*) (E : Proc → Proc → Prop) : Set (Proc → Ω) :=
  { t | ∀ p q, E p q → t p = t q }

/-- **Polarity.** Antitone Galois connection between test classes (⊆) and
    equivalences (refinement): `E` refines `induced Ω T` iff `T ⊆ respects Ω E`. -/
theorem polarity (Ω : Type*) (T : Set (Proc → Ω)) (E : Proc → Proc → Prop) :
    (∀ p q, E p q → induced Ω T p q) ↔ T ⊆ respects Ω E := by
  constructor
  · intro h t ht p q hpq
    exact h p q hpq t ht
  · intro h p q hpq t ht
    exact h ht p q hpq

/-- Every test in `T` respects the equivalence `T` induces (the image fact). -/
theorem test_subset_respects_induced (Ω : Type*) (T : Set (Proc → Ω)) :
    T ⊆ respects Ω (induced Ω T) := by
  intro t ht
  show ∀ p q, induced Ω T p q → t p = t q
  intro p q hpq
  exact hpq t ht

/-- Closure operator on equivalences: `induced Ω ∘ respects Ω`. -/
def cl (Ω : Type*) (E : Proc → Proc → Prop) : Proc → Proc → Prop :=
  induced Ω (respects Ω E)

/-- `cl Ω` is extensive: `E ≤ cl Ω E` (pointwise). -/
theorem cl_extensive (Ω : Type*) (E : Proc → Proc → Prop) (p q : Proc)
    (h : E p q) : cl Ω E p q := by
  intro t ht
  exact ht p q h

/-- `cl Ω` is monotone: `E₁ ≤ E₂ → cl Ω E₁ ≤ cl Ω E₂`. -/
theorem cl_monotone (Ω : Type*) (E₁ E₂ : Proc → Proc → Prop)
    (h : ∀ p q, E₁ p q → E₂ p q) (p q : Proc) (hcl : cl Ω E₁ p q) :
    cl Ω E₂ p q := by
  intro t ht
  exact hcl t (fun a b ha => ht a b (h a b ha))

/-- An equivalence is TESTABLE iff it is exactly "indistinguishability under
    the tests that respect it": a fixed point of `cl Ω`. -/
def Testable (Ω : Type*) (E : Proc → Proc → Prop) : Prop :=
  ∀ p q, cl Ω E p q ↔ E p q

/-- Every induced equivalence is testable (the image of `induced Ω` is contained
    in the fixed points of `cl Ω`). -/
theorem induced_testable (Ω : Type*) (T : Set (Proc → Ω)) :
    Testable Ω (induced Ω T) := by
  intro p q
  constructor
  · -- cl Ω (induced Ω T) p q → induced Ω T p q : every test in T respects it
    intro hcl t ht
    exact hcl t (test_subset_respects_induced Ω T ht)
  · -- induced Ω T p q → cl Ω (induced Ω T) p q : a respecting test agrees on (p,q)
    intro hInd t ht
    exact ht p q hInd

/-- `cl Ω` is idempotent: `cl Ω (cl Ω E) = cl Ω E`. `cl Ω E` lies in the image
    of `induced Ω`, hence is a fixed point by `induced_testable`. -/
theorem cl_idempotent (Ω : Type*) (E : Proc → Proc → Prop) (p q : Proc) :
    cl Ω (cl Ω E) p q ↔ cl Ω E p q := by
  have key : Testable Ω (induced Ω (respects Ω E)) := induced_testable Ω (respects Ω E)
  exact key p q

/-- **Spectrum = image of `induced` = closed elements.** An equivalence is
    testable (a fixed point of `cl Ω`) iff it is exactly the equivalence induced
    by some test class: the Galois-closed equivalences are precisely
    `range (induced Ω)`, witnessed in the forward direction by `T = respects Ω E`. -/
theorem spectrum_eq_closed_elements (Ω : Type*) (E : Proc → Proc → Prop) :
    Testable Ω E ↔ ∃ T : Set (Proc → Ω), induced Ω T = E := by
  constructor
  · intro hE
    refine ⟨respects Ω E, ?_⟩
    show cl Ω E = E
    funext p q
    exact propext (hE p q)
  · rintro ⟨T, rfl⟩
    exact induced_testable Ω T

/-! ## Layer 0.5: the spectrum is a complete lattice

`cl Ω` is a closure operator on the lattice of binary predicates (`Proc → Proc →
Prop`, ordered pointwise: `E₁ ≤ E₂ ↔ ∀ p q, E₁ p q → E₂ p q`). Bundled as a
monotone self-map, Knaster–Tarski gives that its fixed points — the closed
equivalences — form a complete lattice. By `mem_closed_iff_testable` and
`spectrum_eq_closed_elements` these are exactly the testable equivalences,
i.e. the image of `induced Ω`. So the van Glabbeek spectrum is a complete
lattice under refinement: behavioural equivalences admit arbitrary joins/meets. -/

open Function (fixedPoints IsFixedPt)

/-- `cl Ω` bundled as a monotone self-map of the refinement lattice of binary
    predicates. -/
def clHom (Proc Ω : Type*) : (Proc → Proc → Prop) →o (Proc → Proc → Prop) where
  toFun := cl Ω
  monotone' := fun {E₁ E₂} h p q => cl_monotone Ω E₁ E₂ h p q

/-- **Knaster–Tarski (Layer 0.5).** The fixed points of `cl Ω` — the closed
    equivalences — carry a complete-lattice structure under refinement. -/
instance closed_completeLattice (Proc Ω : Type*) :
    CompleteLattice (fixedPoints (clHom Proc Ω)) :=
  inferInstance

/-- A predicate is a fixed point of `cl Ω` iff it is testable: function equality
    `cl Ω E = E` ↔ the pointwise condition `∀ p q, cl Ω E p q ↔ E p q`.
    Together with `spectrum_eq_closed_elements` this pins down the closed
    elements as `Testable` ⇔ `range (induced Ω)`. -/
theorem mem_closed_iff_testable (Proc Ω : Type*) (E : Proc → Proc → Prop) :
    E ∈ fixedPoints (clHom Proc Ω) ↔ Testable Ω E := by
  show cl Ω E = E ↔ Testable Ω E
  constructor
  · rintro h p q
    exact ⟨fun hc => h ▸ hc, fun he => h.symm ▸ he⟩
  · intro h
    funext p q
    exact propext (h p q)

end Spectrum
