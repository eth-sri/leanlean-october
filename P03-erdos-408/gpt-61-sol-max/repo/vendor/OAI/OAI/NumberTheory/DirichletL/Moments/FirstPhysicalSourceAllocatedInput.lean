module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Moments.FirstPhysicalSourceFixedEnergy
public import OAI.NumberTheory.DirichletL.Moments.FirstAllocationGaussEnergy
public import OAI.NumberTheory.DirichletL.Moments.FirstMaskedInput

@[expose] public section

namespace OAI

section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentFirstPhysicalSource
open HeckeFamily CanonicalQuadraticSieve CenteredMomentSourceRow ConcretePrimeRowBridge
open CenteredMomentFirstAmplificationChoice CenteredMomentCommonRadialData
open CenteredMomentAmplificationChildInput CenteredMomentCommonAllocationSum
open CenteredMomentSourceLiveColumn CenteredMomentOriginalChildEnergy
open CenteredMomentSmoothedWindowEnergy CenteredMomentGaussEnergy
open CenteredMomentHeckeColumnWindow CenteredMomentAddedZeroUniform

variable {ι : Type*} [Fintype ι]


lemma commonEnergy_real (D : OriginalData ι)  C   hC 
     τ   t   L   W   K  (hK : 0<K) :
    (commonEnergy D C hC τ t L W K).re =
      CenteredMomentFirstAllocationGaussEnergy.commonEnergy D C hC τ t L W K := (gaussEnergy_hasSum_re Finset.univ
    (sourceGenerator (CenteredMomentFirstSectors.residualPool C hC.1 D.columns))
    (sourceGenerator_supported _) _ W K hK).tsum_eq.symm

section
variable (s : Input ι) (C R seed L : Ideal ActualEisensteinCubic.O) (B : actualAllocations s.pools C) (τ : Character) (t : ℝ)


lemma original_rawVolume     :
    CenteredMomentFirstAllocationGaussEnergy.rawVolume (original s R seed)=volume s := by
  simp [CenteredMomentFirstAllocationGaussEnergy.rawVolume,original,volume]

lemma allocated_input_columns    
          :
    (allocatedData (original s R seed) C L B).columns=
      (original (child s C R B τ t) (R*C) L).columns ∧
    (allocatedData (original s R seed) C L B).beta=
      (original (child s C R B τ t) (R*C) L).beta := OAI.SevenEighths.CenteredMomentAmplificationChildInput.child_columns s C R L B τ t

lemma allocated_input_volume    
          :
    CenteredMomentFirstAllocationGaussEnergy.rawVolume (allocatedData (original s R seed) C L B)=
      volume (child s C R B τ t) := by
  simp only [CenteredMomentFirstAllocationGaussEnergy.rawVolume,allocatedData,original,
    volume,child,commonData,one_mul,div_mul_div_comm]

lemma allocated_input_energy    
           W   K  :
    CenteredMomentFirstAllocationGaussEnergy.allocatedEnergy (original s R seed) C L B τ t W K /
      CenteredMomentFirstAllocationGaussEnergy.rawVolume (allocatedData (original s R seed) C L B)=
      childNormalizedGaussSource s C R L B τ t W K := by
  obtain ⟨hc,hb⟩ := allocated_input_columns s C R seed L B τ t
  unfold CenteredMomentFirstAllocationGaussEnergy.allocatedEnergy
  rw [hc,hb,allocated_input_volume s C R seed L B τ t]
  rfl

end

end SevenEighths.CenteredMomentFirstPhysicalSource

end

end OAI
