module
public import OAI.NumberTheory.DirichletL.Moments.FirstPhysicalSourceOriginalColumn
public import OAI.NumberTheory.DirichletL.Moments.HeckeWindowEnergy

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
open MeasureTheory

namespace SevenEighths.CenteredMomentFirstPhysicalSource
open HeckeFamily CanonicalQuadraticSieve CenteredMomentSourceRow
open CenteredMomentFirstAmplificationChoice CenteredMomentFirstSectors
open CenteredMomentGaussEnergy CenteredMomentHeckeColumnWindow CenteredMomentSecondHeightFamily
open CenteredMomentSourceLiveColumn CenteredMomentCommonAllocationSum CenteredMomentSmooth
open FourierBridge
local notation "O"=>ActualEisensteinCubic.O
variable {ι:Type*}[Fintype ι]
local instance firstWindowDecidableEq : DecidableEq (ι⊕Fin 2):=Classical.decEq _

end SevenEighths.CenteredMomentFirstPhysicalSource

end

end OAI
