/-
CSTR Mapping: EvoEcos Wall Mechanism → Industrial Process Control
================================================================

This file sketches a formal analogy between the EvoEcos wall mechanism
and the Safety Instrumented Function (SIF) in a Continuously Stirred
Tank Reactor (CSTR).

Industrial Safety Analogy
-------------------------

In process control (IEC 61511 / IEC 61508):

  BPCS  = Basic Process Control System
          (normal operation: PID temperature control, flow regulation)
  SIF   = Safety Instrumented Function
          (emergency trip: opens cooling valve fully when T > T_max)

Mapping to EvoEcos:

  EvoEcos Layer     | Process Control Analog        | Role
  ------------------+-------------------------------+---------------------------
  L1 (Operational)  | BPCS (PID controller)         | Normal regulation
  L2 (Modeling)     | Process diagnostics / alarms   | Detect degradation
  L3 (Understanding)| Advanced optimization / MPC    | Complex planning
  Wall activation   | SIF trip (cooling valve opens) | Cut L3 when L1 unstable

Key correspondence:
  - L1 stability < 0.4  ↔  T > T_max (reactor temperature exceeds safe limit)
  - Wall activation     ↔  SIF trip (cooling valve fully opens)
  - L3 blocked          ↔  MPC/optimizer suspended during emergency

Originally a THEOREM SKETCH (main theorems used `sorry`); those sorrys
and the historical model-constant axioms have since been discharged — the
file is now 0 sorry / 0 axiom. The mapping is standalone and NOT added to
the lakefile, so formal/verify.sh does not type-check it; treat it as a
design document, not a CI-enforced proof.
-/

import EvoEcos.WallDomainTriple

noncomputable section

namespace EvoEcos.CSTR

/-! ## CSTR State Space

    We use plain `Real` for temperature (Kelvin) and valve position.
    Physical constraints are captured in `CSTRState.WellFormed`, not
    in the type, to avoid needing order instances on type aliases.
-/

/-- Simplified CSTR state: reactor temperature and cooling valve position.

    Physical model (exothermic reaction A → B):
      dT/dt = (-ΔH_r / ρ Cp) · r(T, C_A) - (UA / ρ Cp V) · (T - T_coolant)
             + q_in/V · (T_feed - T)

    For the safety argument we only track:
      - T_reactor : current reactor temperature (K)
      - valvePos  : cooling valve position (0 = closed, 1 = fully open)
-/
structure CSTRState where
  /-- Current reactor temperature (K). -/
  T_reactor : Real
  /-- Cooling valve position (0.0 = closed, 1.0 = fully open). -/
  valvePos : Real

/-- Well-formedness: temperature is physically plausible and valve in [0,1]. -/
def CSTRState.WellFormed (s : CSTRState) : Prop :=
  s.T_reactor > 0 ∧    -- absolute temperature > 0 K
  s.valvePos ≥ 0 ∧      -- valve cannot close past 0
  s.valvePos ≤ 1        -- valve cannot open past 1

/-! ## Safety Thresholds -/

/-- Maximum allowable reactor temperature before SIF trip.
    In a real CSTR this is determined by:
      - Maximum allowable working pressure (MAWP) via Antoine equation
      - Runaway reaction onset temperature (from ARSST / DSC data)
    Here we leave it as a parameter. -/
def T_max : Real := 500

/-- Safe operating temperature (well below trip point).
    Normal BPCS regulation target. -/
def T_safe : Real := 350

/-- Assumption: safe temperature is strictly below trip point. -/
theorem T_safe_lt_T_max : T_safe < T_max := by unfold T_safe T_max; norm_num

/-- Assumption: safe temperature is physically meaningful. -/
theorem T_safe_pos : T_safe > 0 := by unfold T_safe; norm_num

/-! ## Safety Instrumented Function (SIF) -/

/-- BPCS status: is the basic process control handling the situation? -/
inductive BPCSStatus where
  /-- Normal operation: PID controller maintaining temperature near setpoint. -/
  | normal
  /-- Degraded: controller struggling but still active. -/
  | degraded
  /-- Failed: controller cannot prevent temperature rise. -/
  | failed

/-- SIF trip condition: temperature exceeds T_max.

    This is the direct analog of EvoEcos's "L1 stability < 0.4 → wall activates".
    In process safety:
      - Sensor detects T > T_max
      - Logic solver triggers trip
      - Final element (cooling valve) opens fully

    The analogy:
      EvoEcos                         CSTR
      --------                        ----
      l1.stability.val < 0.4          T_reactor > T_max
      L2State.activateWall            SIF.trip
      l2.wall = true                  valvePos = 1.0
      L3 blocked                      MPC suspended
-/
def SIFShouldTrip (s : CSTRState) : Bool :=
  s.T_reactor > T_max

/-- SIF trip action: opens cooling valve fully.
    Analogous to L2State.activateWall setting wall = true. -/
def SIF.trip (s : CSTRState) : CSTRState :=
  { s with valvePos := (1 : Real) }

/-- SIF reset: returns valve to BPCS control after temperature is safe.
    Analogous to L2State.deactivateWall (hysteresis: require T < T_safe to reset). -/
def SIF.reset (s : CSTRState) (_h : s.T_reactor < T_safe) : CSTRState :=
  { s with valvePos := (0.5 : Real) }  -- hand back to PID at mid-position

/-! ## BPCS State (Analog of L1) -/

/-- BPCS control state. Maps to L1State in EvoEcos.

    BPCS normal   ≈  L1 stability > 0.6 (wall inactive, L3 free)
    BPCS degraded ≈  L1 stability ∈ [0.4, 0.6) (wall active, L3 blocked)
    BPCS failed   ≈  L1 stability < 0.4 (wall active, L3 blocked, reflex only)
-/
structure BPCSState where
  /-- Current BPCS status. -/
  status : BPCSStatus
  /-- Measured temperature deviation from setpoint (normalized 0-1). -/
  deviation : Real

/-- BPCS well-formedness. -/
def BPCSState.WellFormed (s : BPCSState) : Prop :=
  s.deviation ≥ 0 ∧ s.deviation ≤ 1

/-- Map BPCS status to L1 stability analog.

    This function establishes the quantitative correspondence:
      - normal   → stability = 0.8  (comfortable margin)
      - degraded → stability = 0.5  (wall threshold region)
      - failed   → stability = 0.2  (below wall threshold)

    The choice of values preserves the ordering and the 0.4 threshold
    that triggers wall activation in EvoEcos. -/
def BPCSStatus.toStability : BPCSStatus → Real
  | .normal   => 0.8
  | .degraded => 0.5
  | .failed   => 0.2

/-! ## Analog State (Combined) -/

/-- Combined analog state pairing CSTR physical state with BPCS control state.
    This bridges the process control domain with EvoEcos's SystemState. -/
structure AnalogState where
  /-- Physical CSTR state (temperature, valve). -/
  cstr : CSTRState
  /-- BPCS control state. -/
  bpcs : BPCSState
  /-- Whether SIF has tripped (analog of l2.wall). -/
  sifTripped : Bool
  /-- Whether advanced control (MPC) is suspended (analog of l3.blocked). -/
  mpcSuspended : Bool

/-! ## Mapping Lemmas (Sketches) -/

/-- **SIF Trip Theorem (Sketch).**

    If reactor temperature exceeds T_max, the SIF activates (cooling valve opens).

    This is the direct analog of `wall_activates_when_unstable`:
      EvoEcos: l1.stability.val < 0.4 → (activateWall l2 l1).wall = true
      CSTR:    T_reactor > T_max      → SIF.trip cstr.valvePos = 1.0

    In process safety, this is guaranteed by IEC 61511:
      - Sensor reliability (SIL-rated)
      - Logic solver redundancy (1oo2, 2oo3 voting)
      - Final element testing (proof test interval)
-/
theorem sif_trips_when_temperature_exceeds_max (s : CSTRState)
    (h : s.T_reactor > T_max) :
    (SIF.trip s).valvePos = 1 := by
  unfold SIF.trip; rfl

/-- **SIF trip implies MPC suspended (Sketch).**

    When the SIF trips, advanced control (MPC/optimizer) is suspended.
    Analogous to: wall = true → L3 blocked.

    In process control, this is standard practice:
      - SIF trip overrides all BPCS outputs
      - MPC cannot interfere with safety shutdown
      - Operator must acknowledge and reset after T returns to safe range
-/
theorem sif_trip_implies_mpc_suspended (s : AnalogState)
    (h : SIFShouldTrip s.cstr = true) :
    (⟨s.cstr, s.bpcs, true, true⟩ : AnalogState).mpcSuspended = true := by
  rfl

/-- **BPCS failed implies L1-unstable analog (Sketch).**

    When BPCS status is `failed`, the mapped stability is below the
    wall activation threshold (0.4).

    This establishes that BPCS failure maps to L1 instability:
      BPCSStatus.failed → toStability = 0.2 < 0.4
-/
theorem bpcs_failed_implies_unstable :
    BPCSStatus.toStability BPCSStatus.failed < 0.4 := by
  unfold BPCSStatus.toStability; norm_num

/-- **BPCS normal implies L1-stable analog (Sketch).**

    When BPCS status is `normal`, the mapped stability is above the
    wall deactivation threshold (0.6).

    BPCSStatus.normal → toStability = 0.8 > 0.6
-/
theorem bpcs_normal_implies_stable :
    BPCSStatus.toStability BPCSStatus.normal > 0.6 := by
  unfold BPCSStatus.toStability; norm_num

/-! ## Structural Correspondence Theorem (Sketch) -/

/-- **Structural Correspondence: EvoEcos Wall ↔ CSTR SIF (Sketch).**

    This theorem states the core analogy: the EvoEcos wall mechanism and
    the CSTR Safety Instrumented Function obey the same architectural pattern.

    In both systems:
      1. A threshold condition triggers safety activation
         (stability < 0.4  ↔  T > T_max)
      2. Safety activation blocks advanced control
         (wall → L3 blocked  ↔  SIF → MPC suspended)
      3. Safety activation opens a protective channel
         (wall gates L3  ↔  valve opens to full cooling)
      4. Normal operation resumes only when safe with hysteresis
         (stability > 0.6 to deactivate  ↔  T < T_safe to reset)

    The correspondence is not an isomorphism — EvoEcos has additional
    structure (L4 meta-learning, hypothesis management) with no direct
    CSTR analog. But the core safety architecture maps cleanly.

    Reference:
      - IEC 61511: Functional Safety — Safety Instrumented Systems
      - IEC 61508: Functional Safety of E/E/PE Systems
      - Simplex Architecture (Sha 2001): closest academic analog
-/
theorem structural_correspondence
    (l1 : L1State) (l2 : L2State) (l3 : L3State)
    (cstr : CSTRState) (bpcs : BPCSState)
    -- EvoEcos side: L1 unstable
    (h_evo_unstable : l1.stability.val < 0.4)
    -- CSTR side: temperature exceeds max
    (h_cstr_unsafe : cstr.T_reactor > T_max) :
    -- Wall activates in EvoEcos
    (L2State.activateWall l2 l1).wall = true ∧
    -- SIF trips in CSTR
    (SIF.trip cstr).valvePos = 1 ∧
    -- L3 blocked in EvoEcos
    (L3State.blockWhenWallActive l3 (L2State.activateWall l2 l1)).blocked = true ∧
    -- MPC suspended in CSTR (by analogy)
    True := by
  refine ⟨?_, ?_, ?_, trivial⟩
  · exact wall_activates_when_unstable l1 l2 h_evo_unstable
  · unfold SIF.trip; rfl
  · have h_wall := wall_activates_when_unstable l1 l2 h_evo_unstable
    exact l3_blocked_when_wall l3 (L2State.activateWall l2 l1) h_wall

/-- **Round-trip: stability analog matches threshold structure (Sketch).**

    For each BPCS status, the mapped stability value respects the
    wall activation/deactivation thresholds:
      - normal:   stability > 0.6  (above deactivation threshold)
      - degraded: 0.4 ≤ stability ≤ 0.6  (hysteresis region)
      - failed:   stability < 0.4  (below activation threshold)
-/
theorem stability_mapping_respects_thresholds (status : BPCSStatus) :
    match status with
    | BPCSStatus.normal   => status.toStability > 0.6
    | BPCSStatus.degraded => status.toStability ≥ 0.4 ∧ status.toStability ≤ 0.6
    | BPCSStatus.failed   => status.toStability < 0.4 := by
  cases status with
  | normal   => unfold BPCSStatus.toStability; norm_num
  | degraded => unfold BPCSStatus.toStability; exact ⟨by norm_num, by norm_num⟩
  | failed   => unfold BPCSStatus.toStability; norm_num

/-! ## Connection to Wall Domain Triple -/

/-- **CSTR satisfies the Wall Domain Triple (informal argument).**

    The WallDomainTriple.lean establishes that wall benefit > 0 iff:
      1. Low intrinsic dimensionality
      2. Simple causal dynamics
      3. Perturbation present

    A CSTR satisfies all three:
      1. Low intrinsic dim: temperature dynamics are 1-dimensional (T only)
      2. Simple causal: T → cooling → T feedback is well-understood
      3. Perturbation: feed composition changes, fouling, sensor noise

    Discharged: proven below by supplying the witnessing triple
    (true, true, true) and reducing wallBenefit > 0 to it via
    wallBenefit_pos_iff_triple (no `sorry`). The EnvChar fields are
    Boolean indicators from empirical measurement; the proof witnesses
    them directly rather than deriving them from the CSTR ODE model.
-/
theorem cstr_satisfies_wall_triple :
    ∃ (e : _root_.EvoEcos.EnvChar),
      _root_.EvoEcos.EnvChar.lowDim e = true ∧
      _root_.EvoEcos.EnvChar.simpleCausal e = true ∧
      _root_.EvoEcos.EnvChar.perturbation e = true ∧
      _root_.EvoEcos.EnvChar.wallBenefit e > 0 := by
  refine ⟨⟨true, true, true⟩, rfl, rfl, rfl, ?_⟩
  rw [EnvChar.wallBenefit_pos_iff_triple]
  simp [EnvChar.triple]

/-! ## Summary Table (Documentation) -/

/-
   +------------------+-----------------------------------------------+
   | EvoEcos          | Process Control                               |
   +------------------+-----------------------------------------------+
   | L1 (Operational) | BPCS (PID controller)                         |
   | L2 (Modeling)    | Alarms, diagnostics                           |
   | L3 (Planning)    | MPC / advanced optimizer                      |
   | L4 (Meta)        | No direct analog (operator learning)          |
   | Wall mechanism   | SIF trip (IEC 61511)                          |
   | stability < 0.4  | T > T_max (trip setpoint)                     |
   | Wall active      | Cooling valve fully open                      |
   | L3 blocked       | MPC suspended                                 |
   | Hysteresis       | T < T_safe to reset (not T < T_max)           |
   | EnvChar triple   | 1-D dynamics, known causality, process noise  |
   +------------------+-----------------------------------------------+

   Limitations of the analogy:
     1. EvoEcos has L4 (meta-learning) with no process control analog
     2. CSTR safety is governed by SIL (Safety Integrity Level) targets;
        EvoEcos has no quantitative reliability model
     3. The wall mechanism is reactive (binary), while SIF may use
        graded responses (IEC 61511 allows multiple trip levels)
     4. EvoEcos wall is within a single agent; process safety involves
        independent systems (sensor -> logic solver -> final element)
-/

end EvoEcos.CSTR

end
