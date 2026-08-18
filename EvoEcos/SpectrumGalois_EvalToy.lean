import EvoEcos.SpectrumGalois

/-!
# Toy instantiation: eval suites as behavioural-equivalence tests

Reinterprets `Spectrum.induced`/`cl` for AI evaluation instead of process
algebra: `Proc := Model`, `Ω := Bool`, a "test" is one eval probe (a fixed
prompt, scored pass/fail). `induced Ω T` is then "indistinguishable under
every probe in the eval suite `T`" — a testable notion of behavioural
equivalence between models.

The point: `induced Ω T` is always a *testable* equivalence (a fixed point
of `cl Ω`, by `induced_testable`) relative to `T`. That is not the same as
being the *true* equivalence. A probe absent from `T` can separate two
models the suite calls equivalent. Enlarging `T` only refines the induced
equivalence (the antitone direction of `polarity`) — it never coarsens it
further; passing a fixed eval suite consistently certifies nothing beyond
"consistent with the tests that were run."
-/

open Spectrum

namespace Spectrum.EvalToyExample

/-- Three toy models. -/
abbrev Model := Fin 3

def m0 : Model := 0
def m1 : Model := 1
def m2 : Model := 2

/-- Does the model refuse a fixed harmful prompt? -/
def t₁ : Model → Bool
  | 0 => true   -- m0 refuses
  | 1 => true   -- m1 refuses
  | 2 => false  -- m2 complies

/-- Does the model answer a fixed benign question correctly? -/
def t₂ : Model → Bool
  | 0 => true
  | 1 => true
  | 2 => true

/-- A jailbreak probe NOT in the eval suite below: `m0` still refuses,
    `m1` complies. Represents behaviour the suite never checks. -/
def t₃ : Model → Bool
  | 0 => true
  | 1 => false
  | 2 => false

/-- The eval suite actually run: two probes. -/
def evalSuite : Set (Model → Bool) := {t₁, t₂}

/-- Under the suite that's actually run, `m0` and `m1` are testably
    equivalent: they agree on every probe in `evalSuite`. -/
example : induced Bool evalSuite m0 m1 := by
  intro t ht
  rcases ht with rfl | rfl <;> decide

/-- `m2` is correctly distinguished — it fails `t₁`. -/
example : ¬ induced Bool evalSuite m0 m2 := by
  intro h
  exact absurd (h t₁ (Or.inl rfl)) (by decide)

/-- But `m0` and `m1` are not actually equivalent: `t₃`, absent from the
    suite, separates them. -/
example : t₃ m0 ≠ t₃ m1 := by decide

/-- Adding `t₃` to the suite strictly refines the induced equivalence:
    the bigger suite no longer identifies `m0` and `m1`. This is the
    antitone half of `polarity` made concrete — more tests, finer (not
    coarser) equivalence. -/
example : ¬ induced Bool (insert t₃ evalSuite) m0 m1 := by
  intro h
  exact absurd (h t₃ (Or.inl rfl)) (by decide)

end Spectrum.EvalToyExample
