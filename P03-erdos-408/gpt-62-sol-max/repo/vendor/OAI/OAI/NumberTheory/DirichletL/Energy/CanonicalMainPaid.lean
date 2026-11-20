module

public import OAI.NumberTheory.DirichletL.Energy.CanonicalChildBlocks

public import OAI.NumberTheory.DirichletL.Energy.CanonicalUniformReference
public import OAI.NumberTheory.DirichletL.Moments.FirstAmplifiedPaidAdmission
public import OAI.NumberTheory.DirichletL.Energy.AmplifiedRayDictionary

public import OAI.NumberTheory.DirichletL.Energy.FrozenSourceContext

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentEnergyCanonicalMainPaid
open HeckeFamily ConcreteTraceCRT CenteredMomentEnergyAllocatedChildren
open CenteredMomentAllocatedNaturalSource CenteredMomentAllocatedNaturalRadial
open CenteredMomentOriginalRadialComparison CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentRetainedProfile CenteredMomentRadialEligibleEnergy
open CenteredMomentFrozenSourceContext
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]

open CenteredMomentEnergyCanonicalLiveBound CenteredMomentEnergyCanonicalLiveCapacity
open CenteredMomentEnergyCanonicalPaidSource
open CenteredMomentEnergyBandSubtypeTransport
open CenteredMomentFirstAmplifiedCapacityCommon (ratioPenalty)
open CenteredMomentEnergyAllocatedClipped
open CenteredMomentEnergyChildState CenteredMomentSecondNonexceptionalChosenBlock
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentEnergyAllocatedPaid
open CenteredMomentEnergyAllocatedProfiles CenteredMomentEnergyAllocatedZero CenteredMomentInductionEnergy
open CenteredMomentFiniteProfileExceptional CenteredMomentNaturalFixedRaySource
open CenteredMomentCommonRadialData CenteredMomentCommonHeightEnvelope CenteredMomentCommonAllocationSum
open CenteredMomentAllocatedRayDictionary QuadraticInitialBound

open CenteredMomentSectorLocalization
variable (M:Ideal O)[NeZero M]
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

open CenteredMomentEnergyCanonicalUniformReference CenteredMomentEnergyAmplifiedRayDictionary
open CenteredMomentFirstAmplifiedPaidAdmission CenteredMomentFirstAmplifiedCapacityCommon
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentCanonicalFirst CenteredMomentSecondExceptionalFamily CenteredMomentSourceLiveColumn
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical CanonicalQuadraticSieve
open CompletedGauss CanonicalRowCompletion ConcretePrimeRowBridge ActualEisensteinCubic
open CenteredMomentSecondHeightFamily CenteredMomentFirstCanonicalFamily CenteredMomentFirstScale
open CenteredMomentAmplifiedRetainedRadius

omit [DecidableEq α] in
lemma common_raw_caps (src:Input α)(C R:Ideal O)(B:actualAllocations src.pools C)
    (τ:Character)(t F:ℝ)(h₁:src.X₁≤F)(h₂:src.X₂≤F)(h₃:src.Y₁≤F)(h₄:src.Y₂≤F):
    let d:=commonData (withHeight src τ t) C R B
    d.X₁≤F ∧ d.X₂≤F ∧ d.Y₁≤F ∧ d.Y₂≤F:=by
  have hN (j:α⊕Fin 2):(1:ℝ)≤Ideal.absNorm (B.val j):=
    norm_ge_one _ (alloc_ne src C B j)
  exact ⟨(div_le_self src.X₁_pos.le (hN _)).trans h₁,
    (div_le_self src.X₂_pos.le (hN _)).trans h₂,
    (div_le_self src.Y₁_pos.le (hN _)).trans h₃,
    (div_le_self src.Y₂_pos.le (hN _)).trans h₄⟩

end SevenEighths.CenteredMomentEnergyCanonicalMainPaid

end

end OAI
