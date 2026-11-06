module

public import proofs.RAFReactionQuotient.SourceBounds
public import proofs.RAFReactionQuotient.CommutingUniqueness
public import proofs.RAFReactionQuotient.Surjectivity
public import proofs.HordijkSteelThreshold.PolymerCounts
public import proofs.HordijkSteelThreshold.GatewayProbability
public import proofs.HordijkSteelThreshold.NearFullPoolAsymptotics
public import proofs.RAFReactionQuotient.SeedBulk
public import proofs.HordijkSteelThreshold.SprinkledSeedLowerBound
public import proofs.HordijkSteelThreshold.StaticClosureMass
public import proofs.HordijkSteelThreshold.AmbientEscapeBound
public import proofs.HordijkSteelThreshold.SourceTerminalRAF
public import proofs.HordijkSteelThreshold.RecordCylinderDeficit
public import proofs.HordijkSteelThreshold.RecordTargetTrial
public import proofs.HordijkSteelThreshold.SplitPrefixIndependence
public import Mathlib.MeasureTheory.Measure.MeasuredSets
public import Mathlib.MeasureTheory.Constructions.Cylinders
public import proofs.HordijkSteelThreshold.StaticEventContinuity
public import proofs.HordijkSteelThreshold.SourceStaticRAFBound
public import proofs.OverlapCorrectedRAF.Source.KauffmanRepositoryCRS
public import Mathlib
public import proofs.OverlapCorrectedRAF.Source.KauffmanRepositoryModel
public import proofs.OverlapCorrectedRAF.Source.ActualGatewayDock
public import proofs.RAFReactionQuotient.FiniteApproximation
public import proofs.HordijkSteelThreshold.BoundedRAFSeed
public import proofs.HordijkSteelThreshold.PositiveLowerPhase
public import proofs.HordijkSteelThreshold.StaticParameterMonotonicity
public import proofs.HordijkSteelThreshold.ReversibleEscapeProbability
public import Mathlib.Topology.Sequences

@[expose] public section

set_option Elab.async false

namespace RAFReactionQuotient
open Classical Filter MeasureTheory unitInterval HordijkSteelThreshold RAF.Polymer
open OverlapCorrectedRAF.Source
open scoped ENNReal Topology

noncomputable def criticalOpenness (lambda : ℝ) (hlambda : 0 < lambda) : I :=
  ⟨1-Real.exp (-lambda), by
    constructor
    · exact sub_nonneg.mpr $ Real.exp_le_one_iff.mpr $ by linarith
    · linarith [Real.exp_pos $ -lambda]⟩

end RAFReactionQuotient
