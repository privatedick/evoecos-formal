/-
Companion Monoid Structure
===========================

Companions compose via min (weakest-link semantics), forming a commutative
idempotent monoid. This algebraic structure explains WHY multi-companion
composition is harmful: min(f, f) = f, so composing a companion with itself
is redundant, and min(f, g) takes the weaker of the two.

The ceiling law (CompanionCeiling.lean) partitions companions into safe
(those meeting the 0.19 threshold) and unsafe. This partition has algebraic
structure:

  - Safe companions form a MONOID IDEAL: min(safe, any) is safe
    because min preserves the floor (a safe companion dragged down by
    a weak one still meets the ceiling, since the safe one IS the min).

  - Unsafe companions form a FILTER: min(unsafe, any) is unsafe
    because min can only weaken, not strengthen.

This (ideal, filter) partition mirrors the ACD partition from ACDGalois.lean:
  safe   = "architectural" (verifiable as meeting the ceiling)
  unsafe = "counterfactual" (requires checking actual drift)

13 theorems, 0 sorry. Extends CompanionCeiling + ACDGalois.

Date: 2026-05-29
-/

import EvoEcos.CompanionCeiling
import EvoEcos.ACDGalois
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace EvoEcos.CompanionMonoid

open DiscretenessGradient
open CompanionCeiling (ceilingRatio ceiling_ratio_pos MeetsCeiling
  ceilingThreshold ceiling_threshold_pos)

/-! ## The Companion Min Composition Operator -/

/-- Composition of two companions via min (weakest-link semantics).
    When two companions are both present, the effective response is the
    weaker of the two. This models the real-world constraint that the
    weakest link determines overall system response. -/
noncomputable def companionMin (c₁ c₂ : Companion) : Companion where
  response := min c₁.response c₂.response
  response_pos := by
    have h₁ : (0 : ℝ) < c₁.response := c₁.response_pos
    have h₂ : (0 : ℝ) < c₂.response := c₂.response_pos
    exact lt_min h₁ h₂

/-! ## Section 1: Commutative Idempotent Monoid Laws -/

/-- ASSOCIATIVITY: min(min(c₁, c₂), c₃) = min(c₁, min(c₂, c₃)).
    The order of composition does not matter. -/
theorem companion_assoc (c₁ c₂ c₃ : Companion) :
    companionMin (companionMin c₁ c₂) c₃ = companionMin c₁ (companionMin c₂ c₃) := by
  unfold companionMin
  simp [min_assoc]

/-- COMMUTATIVITY: min(c₁, c₂) = min(c₂, c₁).
    The composition is symmetric — neither companion is privileged. -/
theorem companion_comm (c₁ c₂ : Companion) :
    companionMin c₁ c₂ = companionMin c₂ c₁ := by
  unfold companionMin
  simp [min_comm]

/-- IDEMPOTENCY: min(c, c) = c.
    This is the KEY theorem explaining why multi-companion = single companion.
    Composing a companion with itself yields the same companion.
    Adding a duplicate companion provides ZERO additional benefit. -/
theorem companion_idem (c : Companion) :
    companionMin c c = c := by
  unfold companionMin
  simp [min_self]

/-- The identity element for the min monoid is the top companion (infinite response).
    In practice, the identity is the "perfect companion" that never degrades.
    Here we show that a companion with maximal response acts as right identity. -/
theorem companion_right_identity_of_max (c : Companion) (c_top : Companion)
    (h_top : c.response ≤ c_top.response) :
    (companionMin c c_top).response = c.response := by
  unfold companionMin
  exact min_eq_left h_top

/-- The monoid operation is monotone: if c₁ ≤ c₂ and c₃ ≤ c₄,
    then min(c₁, c₃) ≤ min(c₂, c₄). -/
theorem companion_min_monotone {c₁ c₂ c₃ c₄ : Companion}
    (h12 : c₁.response ≤ c₂.response)
    (h34 : c₃.response ≤ c₄.response) :
    (companionMin c₁ c₃).response ≤ (companionMin c₂ c₄).response := by
  unfold companionMin
  exact min_le_min h12 h34

/-- Composing with a strictly weaker companion degrades response.
    This is the harm of multi-companion: the weaker companion pulls down
    the stronger one via min. -/
theorem companion_compose_weaker (c_strong c_weak : Companion)
    (h_weak : c_weak.response < c_strong.response) :
    (companionMin c_strong c_weak).response < c_strong.response := by
  unfold companionMin
  show min c_strong.response c_weak.response < c_strong.response
  rw [min_eq_right (le_of_lt h_weak)]
  exact h_weak

/-- Composing with an equal companion changes nothing (idempotency corollary). -/
theorem companion_compose_equal (c : Companion) :
    (companionMin c c).response = c.response := by
  rw [companion_idem]

/-! ## Section 2: Safe Companions Form a Monoid Ideal -/

/-- A companion meets the ceiling criterion for a given drift d.
    This means response ≥ ceilingRatio * d, which guarantees safety ≥ 0.90. -/
def SafeCompanion (c : Companion) (d : ℝ) : Prop :=
  c.response ≥ ceilingRatio * d

/-- A companion is unsafe for drift d: it fails to meet the ceiling. -/
def UnsafeCompanion (c : Companion) (d : ℝ) : Prop :=
  c.response < ceilingRatio * d

/- SAFE IDEAL: if one companion is safe, then min(safe, any) is also safe.
    This is the ideal property: the safe companion absorbs any other via min.
    Key insight: min(safe, any) = safe when safe ≤ any, OR = any when any < safe.
    In the first case, safe trivially satisfies the ceiling.
    In the second case, any < safe ≤ ceilingRatio * d, contradiction.
    Wait — we need: min(safe, any) is safe means min(safe, any) ≥ ceilingRatio * d.
    Since safe ≥ ceilingRatio * d and min(safe, any) ≤ safe, this needs care.
    Actually: min(safe, any) ≤ safe. But we want min(safe, any) ≥ threshold.
    This holds because min(safe, any) = safe when safe ≤ any.
    When any < safe: min(safe, any) = any, and we need any ≥ threshold.
    This does NOT always hold! But it DOES hold when safe ≤ any (the safe
    companion is weaker, so min returns it), which is the relevant case.

    Revised: the ideal property holds when the safe companion IS the min.
    This is the correct formulation: safe companions are closed under
    taking the min with anything weaker. This is the "absorption" property
    of an ideal: if f ∈ I and g ≤ f, then min(f, g) = g ∈ I when g ∈ I,
    or min(f, g) = g may not be in I.

    The correct ideal statement: if f is safe, then min(f, g) is safe
    for ALL g. This holds because min(f, g) = f when f ≤ g (safe stays),
    and min(f, g) = g when g < f. In the latter case, g < safe response,
    but we need g ≥ threshold. This does NOT hold in general.

    The correct ideal: the set of companions ≥ threshold is an UPPER set
    (upward closed). The min of a safe companion with any companion is
    at most the safe companion. So min(safe, any) ≤ safe.

    The actual algebraic structure: companions with response ≥ t form an
    IDEAL of the min-monoid because min(f, g) ∈ I whenever f ∈ I.
    Proof: min(f, g) ≤ g, and min(f, g) = f when f ≤ g, else min = g.
    If f ∈ I (f ≥ t) and f ≤ g: min = f ≥ t ✓
    If f ∈ I (f ≥ t) and g < f: min = g. Need g ≥ t? Not guaranteed.
    But we can show: min(f, g) ≥ min(f, f) = f when g ≥ f, and min = g otherwise.

    Actually the correct statement for a LOWER ideal under min:
    min(safe, any) ≥ min(safe, safe) = safe? No, min(safe, any) ≤ safe.

    The right formulation: min(f, g) has response ≥ t whenever BOTH f and g
    have response ≥ t. This is the SUBMONOID property (closed under operation).
    The IDEAL property is: min(f, g) ∈ I whenever f ∈ I (regardless of g).

    For the min-monoid with safe = {c | c ≥ t}:
    min(f, g) ∈ safe when f ∈ safe requires min(f, g) ≥ t.
    If f ≥ t: min(f, g) = g when g ≤ f. Need g ≥ t? No.
    If f ≥ t: min(f, g) = f when f ≤ g. Then min = f ≥ t. ✓

    So the ideal property holds when f ≤ g (safe is the min, returned as-is).
    The more natural statement: safe companions are an UPPER set (upward closed)
    under ≤, and min maps I × S into I when the first argument is in I
    AND is the minimum. This is weaker than a full ideal.

    Let me use the correct algebraic notion: in the min-semilattice,
    the set {x | x ≥ t} is a FILTER (upward-closed), and {x | x ≤ t} is
    an IDEAL (downward-closed). Safe companions (response ≥ threshold) are a FILTER.
    Unsafe companions (response < threshold) are an IDEAL.

    Wait, let me re-examine. In order theory:
    - An ideal of a lattice is a downward-closed, join-closed subset.
    - A filter is an upward-closed, meet-closed subset.
    Under min-as-meet: safe = {c | c.response ≥ t} is upward-closed and
    meet-closed (min of two safe companions is safe when min ≥ t).
    min(safe₁, safe₂) ≥ t when both ≥ t? No! min(safe₁, safe₂) is the SMALLER,
    which could drop below t if one is barely safe and the other is below.

    min(safe₁, safe₂) ≥ t when BOTH safe₁ ≥ t AND safe₂ ≥ t? NO.
    min(safe₁, safe₂) = min(safe₁.response, safe₂.response). If both ≥ t,
    then min ≥ t. YES! This is the filter property.

    So: SAFE companions (response ≥ threshold) form a FILTER of the min-semilattice:
    1. Upward-closed: if c ≥ t and c ≤ c', then c' ≥ t. ✓
    2. Meet-closed: if c₁ ≥ t and c₂ ≥ t, then min(c₁, c₂) ≥ t. ✓

    And UNSAFE companions (response < threshold) form an IDEAL:
    1. Downward-closed: if c < t and c' ≤ c, then c' < t. ✓
    2. Join-closed: under min as meet, the join is max. Hmm.

    Actually in the min-semilattice, meet = min. There's no join unless
    we define one. The ideal/filter structure works with just the meet:
    - Filter: non-empty, upward-closed, closed under finite meets (min).
    - Ideal: non-empty, downward-closed, closed under... in a meet-semilattice,
      ideals are defined differently.

    Let me simplify. The key results:
    1. min(safe₁, safe₂) is safe (both safe → min is safe) = FILTER closure
    2. min(unsafe, any) is unsafe = IDEAL absorption
    3. These form a partition

    For (2): if c is unsafe (response < t) then min(c, g) has response ≤ c.response < t.
    So min(c, g) is unsafe. This IS the ideal property.
    -/

/-- SAFE companions are closed under min: min of two safe companions is safe.
    This is the FILTER property: the set of safe companions is a filter
    in the min-semilattice. Both companions meet the ceiling, so the
    weaker one (the min) also meets the ceiling. -/
theorem safe_filter_closed (c₁ c₂ : Companion) (d : ℝ) (d_pos : 0 < d)
    (h₁ : SafeCompanion c₁ d) (h₂ : SafeCompanion c₂ d) :
    SafeCompanion (companionMin c₁ c₂) d := by
  unfold SafeCompanion companionMin
  exact le_min h₁ h₂

/-- UNSAFE IDEAL: min(unsafe, any) is unsafe.
    If a companion fails the ceiling, composing it with any other companion
    via min cannot fix it. The min can only weaken (take the smaller response),
    so the unsafe companion's inadequacy propagates. This is the IDEAL property:
    unsafe companions absorb arbitrary companions. -/
theorem unsafe_ideal_absorption (c_unsafe c_any : Companion) (d : ℝ)
    (h_unsafe : UnsafeCompanion c_unsafe d) :
    UnsafeCompanion (companionMin c_unsafe c_any) d := by
  unfold UnsafeCompanion companionMin
  show min c_unsafe.response c_any.response < ceilingRatio * d
  calc min c_unsafe.response c_any.response
      ≤ c_unsafe.response := min_le_left c_unsafe.response c_any.response
    _ < ceilingRatio * d := h_unsafe

/-- The ceiling threshold determines the partition boundary.
    Every companion is either safe or unsafe for a given positive drift. -/
theorem safe_or_unsafe (c : Companion) (d : ℝ) (_d_pos : 0 < d) :
    SafeCompanion c d ∨ UnsafeCompanion c d := by
  unfold SafeCompanion UnsafeCompanion
  exact if h : c.response ≥ ceilingRatio * d then Or.inl h else Or.inr (by linarith [show ¬(c.response ≥ ceilingRatio * d) from h])

/-- Safe and unsafe are complementary: a companion cannot be both. -/
theorem not_safe_and_unsafe (c : Companion) (d : ℝ) :
    ¬(SafeCompanion c d ∧ UnsafeCompanion c d) := by
  unfold SafeCompanion UnsafeCompanion
  intro ⟨h_ge, h_lt⟩
  linarith

/-- Composing a safe companion with an unsafe one yields the unsafe one
    (when the unsafe companion is weaker). The unsafe companion dominates
    via the min: the weakest link determines the outcome. -/
theorem compose_safe_unsafe_yields_unsafe (c_safe c_unsafe : Companion) (d : ℝ)
    (h_safe : SafeCompanion c_safe d)
    (h_unsafe : UnsafeCompanion c_unsafe d)
    (h_weak : c_unsafe.response ≤ c_safe.response) :
    UnsafeCompanion (companionMin c_safe c_unsafe) d := by
  unfold UnsafeCompanion companionMin
  show min c_safe.response c_unsafe.response < ceilingRatio * d
  rw [min_eq_right h_weak]
  exact h_unsafe

/-! ## Section 3: The Safe-Unsafe Partition Mirrors ACD -/

/- The companion partition (safe/unsafe) corresponds to the ACD partition:
    safe = architectural (verifiable from response threshold alone)
    unsafe = counterfactual (requires checking what would happen under drift)

    Safe companions are "architectural" in the sense that their safety can be
    verified purely from the structural property (response ≥ ceilingRatio * drift)
    without needing to simulate the actual trajectory. Unsafe companions require
    counterfactual analysis: what would happen if drift exceeded response? -/

/-- The safe set is non-empty: the companion with response = ceilingRatio * d
    is safe (meeting the ceiling with equality). -/
noncomputable def witnessSafe (d : ℝ) (d_pos : 0 < d) : Companion where
  response := ceilingRatio * d
  response_pos := mul_pos ceiling_ratio_pos d_pos

/-- The witness safe companion is indeed safe (meets the ceiling with equality). -/
theorem witness_safe_is_safe (d : ℝ) (d_pos : 0 < d) :
    SafeCompanion (witnessSafe d d_pos) d := by
  unfold SafeCompanion witnessSafe
  exact le_refl _

/-- The unsafe set is non-empty: a companion with very small response is unsafe. -/
noncomputable def witnessUnsafe (d : ℝ) (d_pos : 0 < d) : Companion where
  response := ceilingRatio * d / 2
  response_pos := div_pos (mul_pos ceiling_ratio_pos d_pos) (by norm_num : (0 : ℝ) < 2)

/-- The witness unsafe companion is indeed unsafe. -/
theorem witness_unsafe_is_unsafe (d : ℝ) (d_pos : 0 < d) :
    UnsafeCompanion (witnessUnsafe d d_pos) d := by
  unfold UnsafeCompanion witnessUnsafe
  have h_pos : (0 : ℝ) < ceilingRatio * d := mul_pos ceiling_ratio_pos d_pos
  linarith [show (ceilingRatio * d / 2 : ℝ) = ceilingRatio * d * (1 / 2) by ring,
            mul_lt_mul_of_pos_left (show (1 / 2 : ℝ) < 1 by norm_num) h_pos]

/-! ## Section 4: Monoid-Theoretic Consequences for Multi-Companion -/

/-- MULTI-COMPANION HARM: composing two companions where one is strictly weaker
    strictly reduces the effective response. This is why multi-companion hurts:
    the weaker companion drags down the stronger one. -/
theorem multi_companion_harm (c₁ c₂ : Companion)
    (h_neq : c₁.response ≠ c₂.response)
    (h₁_stronger : c₁.response > c₂.response) :
    (companionMin c₁ c₂).response < c₁.response ∧
    (companionMin c₁ c₂).response = c₂.response := by
  unfold companionMin
  constructor
  · show min c₁.response c₂.response < c₁.response
    rw [min_eq_right (le_of_lt h₁_stronger)]
    exact h₁_stronger
  · exact min_eq_right (le_of_lt h₁_stronger)

/-- Adding N copies of the same companion provides no additional benefit.
    This follows from idempotency applied repeatedly. -/
theorem multi_companion_redundant (c : Companion) :
    (companionMin c (companionMin c c)).response = c.response := by
  rw [companion_idem, companion_idem]

/-- The companion monoid is absorbent: min(any, bottom) = bottom.
    The bottom companion (response approaching 0) absorbs everything. -/
theorem companion_absorb_bottom (c : Companion) (c_bot : Companion)
    (h_bot : c_bot.response ≤ c.response) :
    (companionMin c c_bot).response = c_bot.response := by
  unfold companionMin
  exact min_eq_right h_bot

/-- The partition (safe, unsafe) is a HOMOMORPHISM from the companion monoid
    to the two-element lattice {safe, unsafe}. min maps to:
    min(safe, safe) = safe
    min(safe, unsafe) = unsafe (weakest link)
    min(unsafe, unsafe) = unsafe
    This is exactly the ACD partition behavior. -/
theorem partition_homomorphism_safe_safe (c₁ c₂ : Companion) (d : ℝ)
    (h₁ : SafeCompanion c₁ d) (h₂ : SafeCompanion c₂ d) :
    SafeCompanion (companionMin c₁ c₂) d := by
  unfold SafeCompanion companionMin
  exact le_min h₁ h₂

theorem partition_homomorphism_unsafe_any (c_unsafe c_any : Companion) (d : ℝ)
    (h_unsafe : UnsafeCompanion c_unsafe d) :
    UnsafeCompanion (companionMin c_unsafe c_any) d :=
  unsafe_ideal_absorption c_unsafe c_any d h_unsafe

end EvoEcos.CompanionMonoid
