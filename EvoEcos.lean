/-
EvoEcos: Stable Epistemic Bootstrap
====================================

Formal verification of the three-layer cognitive architecture
for AGI safety.

Architecture:
  L1 (Operational) - Survival guarantee, always responds
  L2 (Modeling)    - World model, hypothesis management
  L3 (Understanding) - Deep planning, epistemic bootstrap

Key Properties Proven:
  1. NoCollapse - L1 stability > 0 always
  2. L1AlwaysResponds - Survival guarantee
  3. L3WallInvariant - L3 blocked when L1 unstable
  4. L1Independence - L1 operates without L3
  5. BetaStarPhaseTransition - β* varies by environment type
  6. ValidatedDependency - Safe understanding requires meta-awareness

Usage:
  lake build          # Build the project
  lake env lean       # Run Lean REPL
-/

import EvoEcos.Types
import EvoEcos.Layers
import EvoEcos.Invariants
import EvoEcos.Hierarchy
import EvoEcos.DynamicDelegation
import EvoEcos.PeerCoordination
import EvoEcos.Adversarial
import EvoEcos.AlignmentImpossibility
import EvoEcos.ACD
import EvoEcos.ACDAdversarial
import EvoEcos.ACDMultiAgent
import EvoEcos.ACDTemporal
import EvoEcos.ACDTemporalFormal
import EvoEcos.ACDMetaObservation
import InfoTheory
import Thresholds
import Architecture
import EvoEcos.IBFloor
import EvoEcos.Convergence
import EvoEcos.WallDomainTriple
import EvoEcos.WallDetectorPrecision
import EvoEcos.VacuumSeparability
import EvoEcos.CSTRMapping
import EvoEcos.BoundedCognition
import EvoEcos.ACDGalois
import EvoEcos.CodeObservation
import EvoEcos.DescriptionObservation
import EvoEcos.LayeredObservation
import EvoEcos.SubstrateIsomorphism
import EvoEcos.EffectiveTheory
import EvoEcos.TransitionClassification
import EvoEcos.NetworkContagion
import EvoEcos.InfoTheoreticLimits
import EvoEcos.TopologicalRobustness
import EvoEcos.TopologicalNecessity
import EvoEcos.UnderstandingRatchet
import EvoEcos.MetaLearningUnlock
import EvoEcos.StableGrowthCycle
import EvoEcos.RepeatedGrowthCycle
import EvoEcos.BettiLyapunov
import EvoEcos.CompanionCeiling
import EvoEcos.StrategyOrdering
import EvoEcos.LayerHomology
import EvoEcos.LayerSignaling
import EvoEcos.NoStrangeAttractor
import EvoEcos.CompanionMonoid

import EvoEcos.WallFeasibility

import EvoEcos.OptimalTheta

import EvoEcos.WallActivation

import EvoEcos.WallDebounce


import EvoEcos.WallLiveness

import EvoEcos.WallCostBenefit


import EvoEcos.WallACDConnection

import EvoEcos.EMAConvergence

import EvoEcos.WallFiniteTimeRecovery


import EvoEcos.WallSteadyState


import EvoEcos.ACDCalibration



import EvoEcos.ACDCalibrationBudget


import EvoEcos.WallPhaseRegions

import EvoEcos.WallTransitionDensity

import EvoEcos.EMAFixedPointStructure

import EvoEcos.InfoTheoreticWall
import EvoEcos.EMABasinGeometry
import EvoEcos.L1EnergySufficiency
import EvoEcos.EnergyLyapunov
import EvoEcos.L3Affordability
import EvoEcos.DecisionCost
import EvoEcos.ClampedUpdateCommute
import EvoEcos.PersuasionOperator

-- Modules that were in the tree but imported by no root, so neither CI nor
-- AxiomAudit ever compiled them. Importing them here puts them under the gate.
import EvoEcos.BoundaryACD
import EvoEcos.CBFBarrier
import EvoEcos.CompanionGame
import EvoEcos.CompanionUniversality
import EvoEcos.ComponentTrust
import EvoEcos.ContextualityACD
import EvoEcos.Diversification
import EvoEcos.Duality
import EvoEcos.DynamicBounds
import EvoEcos.FibonacciParity
import EvoEcos.GoalSelector
import EvoEcos.HoldingIdentification
import EvoEcos.IsomorphismCorollaries
import EvoEcos.L1Operational
import EvoEcos.L2Modeling
import EvoEcos.MultiTrackOrchestration
import EvoEcos.ProvabilityLogic
import EvoEcos.ResourceGap
import EvoEcos.RiceBoundary
import EvoEcos.SpectralGapTheorem
import EvoEcos.SpectrumGalois
import EvoEcos.SpectrumGalois_EvalToy
import EvoEcos.ThermostatSetpoint
import EvoEcos.ToolUse
import EvoEcos.ToolUseEcosystem
import EvoEcos.TrustBoundaries
import EvoEcos.UnifiedCompanionTheory
import EvoEcos.WallDelayHarm
import EvoEcos.WallStoppingTime
