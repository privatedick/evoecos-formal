/-
Detector Array Precision
========================

A precision counterpart to `WallDomainTriple.DetectorArray`.

WHY THIS FILE EXISTS.
`DetectorArray.detector_array_guarantee` proves that with N > M corrupted
detectors there EXISTS an uncorrupted signal that the wall detects. It is a pure
RECALL (soundness) statement. Its hypothesis `RespectsBudget` requires that every
uncorrupted signal lie outside the certified radius — i.e. it ASSUMES every honest
detector is a true positive. Nothing on the formal surface bounds false positives,
and the per-detector false-alarm rate `p` does not appear in the guarantee at all.

The empirical consequence (experiment_detector_array_precision.py, 5/5 H):
`experiment_detector_array.py` charges damage only when nothing fires and never
penalises firing, so a detector that fires unconditionally attains detection 1.000
and damage 0.000 — it weakly dominates the real detector at 14/14 published cells.
"More detectors is better" is an identity of OR-combination under recall-only
scoring, not a property of detector arrays.

This file states the missing half. For an OR-array of `k` independent honest
detectors with per-detector rates `p` (false alarm) and `q` (hit), `p < q < 1`:

    arrayTPR k = 1 - (1-q)^k        arrayFPR k = 1 - (1-p)^k

Both are strictly increasing in `k`. With miss cost normalised to 1, attack base
rate `att`, false-alarm cost `lam = C_fa / C_miss` and per-detector upkeep `gam`:

    cost k = att * (1-q)^k + (1-att) * lam * (1 - (1-p)^k) + gam * k

The results below are a DICHOTOMY:

  * `cost_succ_lt_of_free_false_alarms` — when `lam = gam = 0` (false alarms are
    free) cost strictly decreases in `k`: monotone "more is better" holds. This is
    exactly the corner the published experiment measured.
  * `exists_eventually_cost_increasing` — when `lam > 0` cost is EVENTUALLY
    strictly increasing, so monotonicity fails.
  * `exists_optimal_array_size` — consequently a globally optimal finite `k₀`
    exists. The array has a finite optimum, matching the observed ~5-6 antiphage
    defence systems per bacterial genome rather than an unbounded stack.

The optimum is the `k` at which `cost_succ_sub` changes sign. For `gam = 0` — the
regime the simulation swept — solving that identity gives the closed form

  k* = ln( (1-att)·lam·p / (att·q) ) / ln( (1-q)/(1-p) ),

and `cost_optimal_at_ceil_kStar` proves the minimiser is exactly `⌈k*⌉₊`. Because
`pow_le_iff_kStar_le` is an `iff`, a concrete optimum can be pinned by comparing
`r^0` and `r^1` to `ε` — arithmetic, no logarithm evaluated. For the witness that
yields `⌈k*⌉₊ = 1`, matching the simulation cell `(p, lam, att) = (0.05, 1, 0.30)`.

With `gam > 0` the marginal condition is transcendental in a second way and admits
no such closed form; only `exists_optimal_array_size` covers that case.

Runtime coupling (src/experiments/experiment_detector_array_precision.py):
  theory-only (no runtime analog — these bound a CONFIRMED result, they do not
  gate a layer transition):
    arrayFPR_strict_mono, arrayTPR_strict_mono, no_free_recall
    cost_succ_sub, cost_succ_lt_of_free_false_alarms
    exists_eventually_cost_increasing, exists_optimal_array_size
    kStar, pow_le_iff_kStar_le, cost_optimal_at_ceil_kStar
    projectBar_optimal_array_size_is_one
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

noncomputable section

namespace EvoEcos

namespace WallDetectorPrecision

/-- Per-detector operating point of an honest detector in the array.
    `p` is the false-alarm rate on a clean episode, `q` the hit rate on an
    attack episode. A useful detector is better than chance at separating the
    two, hence `p < q`; neither is certain, hence `q < 1`. -/
structure DetectorSpec where
  /-- Per-detector false-alarm rate on a clean episode. -/
  p : ℝ
  /-- Per-detector hit rate on an attack episode. -/
  q : ℝ
  /-- False alarms are possible: a perfectly precise detector is the degenerate
      corner that makes the published monotonicity true. -/
  p_pos : 0 < p
  /-- The detector is informative: it fires more often under attack than clean. -/
  p_lt_q : p < q
  /-- Detection is not certain. -/
  q_lt_one : q < 1

namespace DetectorSpec

variable (d : DetectorSpec)

theorem q_pos : 0 < d.q := lt_trans d.p_pos d.p_lt_q

theorem p_lt_one : d.p < 1 := lt_trans d.p_lt_q d.q_lt_one

theorem one_sub_p_pos : 0 < 1 - d.p := by have := d.p_lt_one; linarith

theorem one_sub_q_pos : 0 < 1 - d.q := by have := d.q_lt_one; linarith

theorem one_sub_p_lt_one : 1 - d.p < 1 := by have := d.p_pos; linarith

theorem one_sub_q_lt_one : 1 - d.q < 1 := by have := d.q_pos; linarith

/-- The survival ratio `(1-q)/(1-p)` lies strictly in `(0,1)`: an attack survives
    a single honest detector less often than a clean episode does. This is the
    engine of the whole file — it is why recall saturates faster than the
    false-alarm mass accumulates. -/
theorem one_sub_q_lt_one_sub_p : 1 - d.q < 1 - d.p := by
  have := d.p_lt_q; linarith

end DetectorSpec

/-! ## Array rates under OR-combination -/

/-- Probability that at least one of `k` honest detectors fires on a CLEAN
    episode — the array's false-alarm rate. -/
def arrayFPR (d : DetectorSpec) (k : ℕ) : ℝ := 1 - (1 - d.p) ^ k

/-- Probability that at least one of `k` honest detectors fires on an ATTACK
    episode — the array's recall. -/
def arrayTPR (d : DetectorSpec) (k : ℕ) : ℝ := 1 - (1 - d.q) ^ k

/-- A base strictly between 0 and 1 has strictly decreasing powers. -/
theorem pow_succ_lt (a : ℝ) (h0 : 0 < a) (h1 : a < 1) (k : ℕ) : a ^ (k + 1) < a ^ k := by
  have hk : (0 : ℝ) < a ^ k := pow_pos h0 k
  calc a ^ (k + 1) = a ^ k * a := pow_succ a k
    _ < a ^ k * 1 := by exact (mul_lt_mul_of_pos_left h1 hk)
    _ = a ^ k := mul_one _

/-- Powers of a base in `(0,1)` are strictly antitone. -/
theorem pow_strictAnti (a : ℝ) (h0 : 0 < a) (h1 : a < 1) : StrictAnti (fun k : ℕ => a ^ k) :=
  strictAnti_nat_of_succ_lt (fun k => pow_succ_lt a h0 h1 k)

/-- **Precision strictly degrades with array size.** Every detector added to the
    OR-array strictly raises the false-alarm rate. There is no free detector. -/
theorem arrayFPR_strict_mono (d : DetectorSpec) : StrictMono (arrayFPR d) := by
  intro j k hjk
  have h := pow_strictAnti (1 - d.p) d.one_sub_p_pos d.one_sub_p_lt_one hjk
  simp only [arrayFPR]
  linarith

/-- Recall strictly improves with array size (the published direction). -/
theorem arrayTPR_strict_mono (d : DetectorSpec) : StrictMono (arrayTPR d) := by
  intro j k hjk
  have h := pow_strictAnti (1 - d.q) d.one_sub_q_pos d.one_sub_q_lt_one hjk
  simp only [arrayTPR]
  linarith

/-- **No free recall.** Any array enlargement that strictly improves recall also
    strictly worsens precision. Recall and false alarms cannot be traded
    independently, which is precisely what a recall-only metric hides. -/
theorem no_free_recall (d : DetectorSpec) {j k : ℕ} (hjk : j < k) :
    arrayTPR d j < arrayTPR d k ∧ arrayFPR d j < arrayFPR d k :=
  ⟨arrayTPR_strict_mono d hjk, arrayFPR_strict_mono d hjk⟩

/-- Every nonempty array carries strictly positive false-alarm mass. -/
theorem arrayFPR_pos (d : DetectorSpec) (k : ℕ) (hk : 0 < k) : 0 < arrayFPR d k := by
  have h : (1 - d.p) ^ k < (1 - d.p) ^ 0 :=
    pow_strictAnti (1 - d.p) d.one_sub_p_pos d.one_sub_p_lt_one hk
  simp only [arrayFPR, pow_zero] at *
  linarith

/-! ## Expected cost, and the failure of monotonicity -/

/-- Expected per-episode cost of an OR-array of `k` honest detectors.
    Miss cost is normalised to 1; `att` is the attack base rate, `lam` the
    false-alarm cost relative to a miss, `gam` the per-detector upkeep. -/
def cost (d : DetectorSpec) (att lam gam : ℝ) (k : ℕ) : ℝ :=
  att * (1 - d.q) ^ k + (1 - att) * lam * (1 - (1 - d.p) ^ k) + gam * (k : ℝ)

/-- **Marginal-cost identity.** The exact gain from adding one detector: a recall
    term that shrinks like `(1-q)^k`, a false-alarm term that shrinks like
    `(1-p)^k`, and a constant upkeep. Since `(1-q)^k` decays strictly faster, the
    negative term dies first — that is the whole mechanism. -/
theorem cost_succ_sub (d : DetectorSpec) (att lam gam : ℝ) (k : ℕ) :
    cost d att lam gam (k + 1) - cost d att lam gam k
      = (1 - att) * lam * d.p * (1 - d.p) ^ k - att * d.q * (1 - d.q) ^ k + gam := by
  simp only [cost, pow_succ, Nat.cast_add, Nat.cast_one]
  ring

/-- **The published regime.** When false alarms are free (`lam = 0`) and detectors
    are free (`gam = 0`), cost strictly decreases in `k`: more detectors is
    strictly better, without bound. `experiment_detector_array.py` measured
    exactly this corner, which is why it found monotonicity. -/
theorem cost_succ_lt_of_free_false_alarms (d : DetectorSpec) {att : ℝ} (hatt : 0 < att)
    (k : ℕ) : cost d att 0 0 (k + 1) < cost d att 0 0 k := by
  have hid := cost_succ_sub d att 0 0 k
  have hq : 0 < att * d.q * (1 - d.q) ^ k :=
    mul_pos (mul_pos hatt d.q_pos) (pow_pos d.one_sub_q_pos k)
  linarith

/-- **The bound.** With any strictly positive false-alarm cost, the marginal
    detector is eventually harmful: beyond some `K`, each added detector strictly
    increases expected cost. Monotone "more is better" fails.

    Mechanism: the recall gain `att·q·(1-q)^k` decays strictly faster than the
    false-alarm penalty `(1-att)·lam·p·(1-p)^k`, because `(1-q)/(1-p) < 1`. -/
theorem exists_eventually_cost_increasing (d : DetectorSpec) {att lam gam : ℝ}
    (hatt : 0 < att) (hatt1 : att < 1) (hlam : 0 < lam) (hgam : 0 ≤ gam) :
    ∃ K : ℕ, ∀ k, K ≤ k → cost d att lam gam k < cost d att lam gam (k + 1) := by
  set r : ℝ := (1 - d.q) / (1 - d.p) with hr_def
  have hp_pos := d.one_sub_p_pos
  have hq_pos := d.one_sub_q_pos
  have hr_pos : 0 < r := div_pos hq_pos hp_pos
  have hr_lt_one : r < 1 := (div_lt_one hp_pos).mpr d.one_sub_q_lt_one_sub_p
  -- The threshold the survival ratio must fall below.
  set ε : ℝ := ((1 - att) * lam * d.p) / (att * d.q) with hε_def
  have hden : 0 < att * d.q := mul_pos hatt d.q_pos
  have hnum : 0 < (1 - att) * lam * d.p :=
    mul_pos (mul_pos (by linarith) hlam) d.p_pos
  have hε_pos : 0 < ε := div_pos hnum hden
  obtain ⟨K, hK⟩ := exists_pow_lt_of_lt_one hε_pos hr_lt_one
  refine ⟨K, fun k hk => ?_⟩
  -- r^k ≤ r^K < ε
  have hrk : r ^ k ≤ r ^ K := pow_le_pow_of_le_one (le_of_lt hr_pos) (le_of_lt hr_lt_one) hk
  have hrk_lt : r ^ k < ε := lt_of_le_of_lt hrk hK
  -- Rewrite (1-q)^k = r^k * (1-p)^k.
  have hpow : (1 - d.q) ^ k = r ^ k * (1 - d.p) ^ k := by
    rw [hr_def, div_pow, div_mul_cancel₀]
    exact ne_of_gt (pow_pos hp_pos k)
  have hpk_pos : (0 : ℝ) < (1 - d.p) ^ k := pow_pos hp_pos k
  -- att*q*(1-q)^k = (att*q*r^k) * (1-p)^k < ((1-att)*lam*p) * (1-p)^k
  have hkey : att * d.q * (1 - d.q) ^ k < (1 - att) * lam * d.p * (1 - d.p) ^ k := by
    have hlt : att * d.q * r ^ k < (1 - att) * lam * d.p := by
      have := (mul_lt_mul_of_pos_left hrk_lt hden)
      rwa [hε_def, mul_div_cancel₀ _ (ne_of_gt hden)] at this
    calc att * d.q * (1 - d.q) ^ k
        = (att * d.q * r ^ k) * (1 - d.p) ^ k := by rw [hpow]; ring
      _ < ((1 - att) * lam * d.p) * (1 - d.p) ^ k := by
          exact (mul_lt_mul_of_pos_right hlt hpk_pos)
  have hid := cost_succ_sub d att lam gam k
  linarith

/-- **A finite optimal array size exists.** Cost is eventually strictly
    increasing, so it attains a global minimum at some finite `k₀`. Stacking
    detectors without bound is strictly suboptimal whenever false alarms cost
    anything at all. -/
theorem exists_optimal_array_size (d : DetectorSpec) {att lam gam : ℝ}
    (hatt : 0 < att) (hatt1 : att < 1) (hlam : 0 < lam) (hgam : 0 ≤ gam) :
    ∃ k₀ : ℕ, ∀ k : ℕ, cost d att lam gam k₀ ≤ cost d att lam gam k := by
  obtain ⟨K, hK⟩ := exists_eventually_cost_increasing d hatt hatt1 hlam hgam
  -- Beyond K the cost never dips below its value at K.
  have hmono : ∀ k, K ≤ k → cost d att lam gam K ≤ cost d att lam gam k := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => exact le_refl _
    | succ n hn ih => exact le_trans ih (le_of_lt (hK n hn))
  -- Minimise over the finite prefix {0, …, K}.
  obtain ⟨k₀, hk₀mem, hk₀⟩ :=
    Finset.exists_min_image (Finset.range (K + 1)) (cost d att lam gam)
      ⟨K, Finset.mem_range.mpr (Nat.lt_succ_self K)⟩
  refine ⟨k₀, fun k => ?_⟩
  rcases lt_or_ge k (K + 1) with h | h
  · exact hk₀ k (Finset.mem_range.mpr h)
  · have hKk : K ≤ k := Nat.le_of_succ_le h
    exact le_trans (hk₀ K (Finset.mem_range.mpr (Nat.lt_succ_self K))) (hmono k hKk)

/-- **The dichotomy, stated as one theorem.** For a fixed informative detector,
    either false alarms are free and every added detector strictly helps, or they
    cost something and the array has a finite optimum. `detector_array`
    [CONFIRMED] established the first disjunct and was read as if it established
    the second's negation. -/
theorem monotone_or_finite_optimum (d : DetectorSpec) {att lam gam : ℝ}
    (hatt : 0 < att) (hatt1 : att < 1) (hgam : 0 ≤ gam) :
    (lam = 0 ∧ gam = 0 → ∀ k, cost d att lam gam (k + 1) < cost d att lam gam k) ∧
    (0 < lam → ∃ k₀ : ℕ, ∀ k : ℕ, cost d att lam gam k₀ ≤ cost d att lam gam k) := by
  constructor
  · rintro ⟨hl, hg⟩ k
    subst hl; subst hg
    exact cost_succ_lt_of_free_false_alarms d hatt k
  · intro hlam
    exact exists_optimal_array_size d hatt hatt1 hlam hgam

/-! ## The closed form for the optimal array size

`exists_optimal_array_size` asserts that a minimiser exists but says nothing about
where it is. This section locates it exactly, for zero per-detector upkeep
(`gam = 0`) — the regime the simulation swept. The transcendental content is
confined to `kStar`; every downstream result is an `iff`, so a concrete optimum
can be pinned by instantiating at two integers without evaluating a logarithm. -/

/-- `r = (1-q)/(1-p) ∈ (0,1)`: the rate at which an attack out-survives a clean
    episode across one honest detector. -/
def survivalRatio (d : DetectorSpec) : ℝ := (1 - d.q) / (1 - d.p)

/-- `ε = (1-att)·lam·p / (att·q)`: the level the survival ratio must fall below
    before the marginal detector starts costing more than it earns. -/
def marginThreshold (d : DetectorSpec) (att lam : ℝ) : ℝ :=
  ((1 - att) * lam * d.p) / (att * d.q)

/-- **The closed form.** `k* = ln ε / ln r`. Below it the marginal detector pays
    for itself; above it, it does not. -/
def kStar (d : DetectorSpec) (att lam : ℝ) : ℝ :=
  Real.log (marginThreshold d att lam) / Real.log (survivalRatio d)

theorem survivalRatio_pos (d : DetectorSpec) : 0 < survivalRatio d :=
  div_pos d.one_sub_q_pos d.one_sub_p_pos

theorem survivalRatio_lt_one (d : DetectorSpec) : survivalRatio d < 1 :=
  (div_lt_one d.one_sub_p_pos).mpr d.one_sub_q_lt_one_sub_p

/-- The engine, in log form: `ln r < 0`. Every sign flip below comes from this. -/
theorem log_survivalRatio_neg (d : DetectorSpec) : Real.log (survivalRatio d) < 0 :=
  Real.log_neg (survivalRatio_pos d) (survivalRatio_lt_one d)

theorem marginThreshold_pos (d : DetectorSpec) {att lam : ℝ}
    (hatt : 0 < att) (hatt1 : att < 1) (hlam : 0 < lam) :
    0 < marginThreshold d att lam :=
  div_pos (mul_pos (mul_pos (by linarith) hlam) d.p_pos) (mul_pos hatt d.q_pos)

/-- The marginal cost factors as `(1-p)^k · ((1-att)·lam·p − att·q·r^k)`.
    The left factor is always positive, so the sign is carried entirely by the
    bracket — and `r^k` is the only part that moves with `k`. -/
theorem cost_succ_sub_factored (d : DetectorSpec) (att lam : ℝ) (k : ℕ) :
    cost d att lam 0 (k + 1) - cost d att lam 0 k
      = (1 - d.p) ^ k * ((1 - att) * lam * d.p - att * d.q * survivalRatio d ^ k) := by
  have hpow : (1 - d.q) ^ k = survivalRatio d ^ k * (1 - d.p) ^ k := by
    rw [survivalRatio, div_pow, div_mul_cancel₀]
    exact ne_of_gt (pow_pos d.one_sub_p_pos k)
  rw [cost_succ_sub, hpow]
  ring

/-- Comparing `r^k` to `ε` is exactly comparing `k` to `k*`. This is the bridge
    between the algebra and the closed form, and it is an `iff` in both
    directions — which is what lets a concrete optimum be computed. -/
theorem pow_le_iff_kStar_le (d : DetectorSpec) {att lam : ℝ}
    (hatt : 0 < att) (hatt1 : att < 1) (hlam : 0 < lam) (k : ℕ) :
    survivalRatio d ^ k ≤ marginThreshold d att lam ↔ kStar d att lam ≤ (k : ℝ) := by
  have hrk : (0 : ℝ) < survivalRatio d ^ k := pow_pos (survivalRatio_pos d) k
  have hε : 0 < marginThreshold d att lam := marginThreshold_pos d hatt hatt1 hlam
  rw [← Real.log_le_log_iff hrk hε, Real.log_pow, kStar,
    div_le_iff_of_neg (log_survivalRatio_neg d)]

/-- Strict form: `r^k < ε ↔ k* < k`. -/
theorem pow_lt_iff_kStar_lt (d : DetectorSpec) {att lam : ℝ}
    (hatt : 0 < att) (hatt1 : att < 1) (hlam : 0 < lam) (k : ℕ) :
    survivalRatio d ^ k < marginThreshold d att lam ↔ kStar d att lam < (k : ℝ) := by
  have hrk : (0 : ℝ) < survivalRatio d ^ k := pow_pos (survivalRatio_pos d) k
  have hε : 0 < marginThreshold d att lam := marginThreshold_pos d hatt hatt1 hlam
  rw [← Real.log_lt_log_iff hrk hε, Real.log_pow, kStar,
    div_lt_iff_of_neg (log_survivalRatio_neg d)]

/-- **The optimum is `⌈k*⌉₊`.** Cost strictly decreases below the closed form and
    weakly increases above it, so the least natural number at or beyond `k*` is a
    global minimiser. This upgrades `exists_optimal_array_size` from "a minimiser
    exists" to "here it is". -/
theorem cost_optimal_at_ceil_kStar (d : DetectorSpec) {att lam : ℝ}
    (hatt : 0 < att) (hatt1 : att < 1) (hlam : 0 < lam) :
    ∀ k : ℕ, cost d att lam 0 ⌈kStar d att lam⌉₊ ≤ cost d att lam 0 k := by
  set C := ⌈kStar d att lam⌉₊ with hC
  have hden : 0 < att * d.q := mul_pos hatt d.q_pos
  have hpk : ∀ j : ℕ, (0 : ℝ) < (1 - d.p) ^ j := fun j => pow_pos d.one_sub_p_pos j
  -- At or above the closed form the marginal detector never pays for itself.
  have hup : ∀ j : ℕ, C ≤ j → cost d att lam 0 j ≤ cost d att lam 0 (j + 1) := by
    intro j hj
    have hkj : kStar d att lam ≤ (j : ℝ) :=
      le_trans (Nat.le_ceil _) (by exact_mod_cast hj)
    have hpow : survivalRatio d ^ j ≤ marginThreshold d att lam :=
      (pow_le_iff_kStar_le d hatt hatt1 hlam j).mpr hkj
    rw [marginThreshold, le_div_iff₀ hden] at hpow
    have hfac := cost_succ_sub_factored d att lam j
    nlinarith [hpk j, hpow]
  -- Strictly below the closed form each added detector strictly pays for itself.
  have hdown : ∀ j : ℕ, j < C → cost d att lam 0 (j + 1) ≤ cost d att lam 0 j := by
    intro j hj
    have hjk : (j : ℝ) < kStar d att lam := Nat.lt_ceil.mp hj
    have hgt : marginThreshold d att lam < survivalRatio d ^ j := by
      by_contra hcon
      exact absurd ((pow_le_iff_kStar_le d hatt hatt1 hlam j).mp (not_lt.mp hcon))
        (not_le.mpr hjk)
    rw [marginThreshold, div_lt_iff₀ hden] at hgt
    have hfac := cost_succ_sub_factored d att lam j
    nlinarith [hpk j, hgt]
  -- Nondecreasing from C upward.
  have hmono : ∀ k, C ≤ k → cost d att lam 0 C ≤ cost d att lam 0 k := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => exact le_refl _
    | succ n hn ih => exact le_trans ih (hup n hn)
  -- Antitone on the prefix [0, C]: walk down the gap.
  have hgap : ∀ t m : ℕ, m + t ≤ C → cost d att lam 0 (m + t) ≤ cost d att lam 0 m := by
    intro t
    induction t with
    | zero => intro m _; exact le_refl _
    | succ s ih =>
        intro m hm
        have hs : m + s < C := by omega
        have hstep : cost d att lam 0 (m + s + 1) ≤ cost d att lam 0 (m + s) :=
          hdown (m + s) hs
        have hrec : cost d att lam 0 (m + s) ≤ cost d att lam 0 m := ih m (by omega)
        have heq : m + (s + 1) = m + s + 1 := by omega
        rw [heq]
        exact le_trans hstep hrec
  intro k
  rcases Nat.lt_or_ge k C with h | h
  · have hkC : k + (C - k) = C := by omega
    have hle := hgap (C - k) k (by omega)
    rw [hkC] at hle
    exact hle
  · exact hmono k h

/-! ## Inhabitation witness

Everything above quantifies over `DetectorSpec`. Without a witness the results
would be vacuously true, which no sorry/axiom/tautology gate would catch. The
witness is not arbitrary: `p = 1/20` is exactly the clean false-positive ceiling
that `l2_malignant_leak_detector` [CONFIRMED] imposes on a detector, and `q = 9/10`
is the per-detector hit rate used in the simulation. -/

/-- A detector meeting the project's own precision bar (`clean FP < 0.05`). -/
def projectBar : DetectorSpec where
  p := 1 / 20
  q := 9 / 10
  p_pos := by norm_num
  p_lt_q := by norm_num
  q_lt_one := by norm_num

/-- The structure is inhabited, so the theorems above are not vacuous. -/
instance : Nonempty DetectorSpec := ⟨projectBar⟩

/-- Concrete instantiation: a detector at the project's precision bar, an attack
    base rate of `3/10`, and a false alarm costing the same as a miss (`lam = 1`)
    admits a finite optimal array size. Stacking such detectors without bound is
    strictly suboptimal — the simulation puts the optimum at `k* = 1` here. -/
theorem projectBar_has_finite_optimum :
    ∃ k₀ : ℕ, ∀ k : ℕ,
      cost projectBar (3 / 10) 1 0 k₀ ≤ cost projectBar (3 / 10) 1 0 k :=
  exists_optimal_array_size projectBar (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- The same detector, with false alarms declared free, instead strictly improves
    forever. The two corollaries share a witness and differ only in `lam`, which
    isolates the false-alarm cost as the sole cause of the finite optimum. -/
theorem projectBar_monotone_when_false_alarms_free (k : ℕ) :
    cost projectBar (3 / 10) 0 0 (k + 1) < cost projectBar (3 / 10) 0 0 k :=
  cost_succ_lt_of_free_false_alarms projectBar (by norm_num) k

/-! ### Pinning the optimum without evaluating a logarithm

`kStar` is transcendental, but `pow_le_iff_kStar_le` is an `iff`, so bracketing
`k*` between two integers only needs `r^0` and `r^1` compared to `ε` — pure
arithmetic. This is what makes the closed form usable rather than decorative. -/

theorem projectBar_survivalRatio : survivalRatio projectBar = 2 / 19 := by
  norm_num [survivalRatio, projectBar]

theorem projectBar_marginThreshold : marginThreshold projectBar (3 / 10) 1 = 7 / 54 := by
  norm_num [marginThreshold, projectBar]

/-- `0 < k* ≤ 1` for the witness, hence `⌈k*⌉₊ = 1`. Established from
    `r^1 ≤ ε` (so `k* ≤ 1`) and `¬(r^0 ≤ ε)` (so `k* > 0`); both are `norm_num`
    facts about `2/19` and `7/54`. No logarithm is ever evaluated. -/
theorem projectBar_ceil_kStar_eq_one : ⌈kStar projectBar (3 / 10) 1⌉₊ = 1 := by
  have hatt : (0 : ℝ) < 3 / 10 := by norm_num
  have hatt1 : (3 : ℝ) / 10 < 1 := by norm_num
  have hlam : (0 : ℝ) < 1 := by norm_num
  have hle : kStar projectBar (3 / 10) 1 ≤ (1 : ℝ) := by
    have h := (pow_le_iff_kStar_le projectBar hatt hatt1 hlam 1)
    rw [projectBar_survivalRatio, projectBar_marginThreshold] at h
    have : ((2 : ℝ) / 19) ^ (1 : ℕ) ≤ 7 / 54 := by norm_num
    exact_mod_cast h.mp this
  have hpos : (0 : ℝ) < kStar projectBar (3 / 10) 1 := by
    by_contra hcon
    replace hcon : kStar projectBar (3 / 10) 1 ≤ 0 := not_lt.mp hcon
    have h := (pow_le_iff_kStar_le projectBar hatt hatt1 hlam 0)
    rw [projectBar_survivalRatio, projectBar_marginThreshold] at h
    have hbad : ((2 : ℝ) / 19) ^ (0 : ℕ) ≤ 7 / 54 := h.mpr (by exact_mod_cast hcon)
    rw [pow_zero] at hbad
    norm_num at hbad
  have h1 : ⌈kStar projectBar (3 / 10) 1⌉₊ ≤ 1 := Nat.ceil_le.mpr (by exact_mod_cast hle)
  have h2 : 0 < ⌈kStar projectBar (3 / 10) 1⌉₊ := Nat.lt_ceil.mpr (by exact_mod_cast hpos)
  omega

/-- **The optimum is exactly one detector**, for a detector at the project's own
    precision bar with an attack base rate of `3/10` and a false alarm costing the
    same as a miss. The simulation reports `k* = 1` at `(p, lam, pi) = (0.05, 1,
    0.30)`; this is that cell, proved. -/
theorem projectBar_optimal_array_size_is_one (k : ℕ) :
    cost projectBar (3 / 10) 1 0 1 ≤ cost projectBar (3 / 10) 1 0 k := by
  have h := cost_optimal_at_ceil_kStar projectBar
    (by norm_num : (0 : ℝ) < 3 / 10) (by norm_num : (3 : ℝ) / 10 < 1)
    (by norm_num : (0 : ℝ) < 1) k
  rwa [projectBar_ceil_kStar_eq_one] at h

end WallDetectorPrecision

end EvoEcos
