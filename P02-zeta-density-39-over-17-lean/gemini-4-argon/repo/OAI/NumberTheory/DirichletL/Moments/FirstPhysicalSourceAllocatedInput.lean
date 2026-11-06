module
public import OAI.NumberTheory.DirichletL.Moments.FirstPhysicalSourceFixedEnergy
public import OAI.NumberTheory.DirichletL.Moments.FirstAllocationGaussEnergy
public import OAI.NumberTheory.DirichletL.Moments.FirstMaskedInput

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentFirstPhysicalSource
open HeckeFamily CanonicalQuadraticSieve CenteredMomentSourceRow ConcretePrimeRowBridge CenteredMomentFirstAmplificationChoice CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput CenteredMomentCommonAllocationSum CenteredMomentSourceLiveColumn CenteredMomentOriginalChildEnergy CenteredMomentSmoothedWindowEnergy CenteredMomentGaussEnergy CenteredMomentHeckeColumnWindow CenteredMomentAddedZeroUniform
variable {ι : Type*} [Fintype ι]

lemma commonEnergy_real (D : OriginalData ι) (C : Ideal O) (hC : Supported C)
    (τ : Character) (t : ℝ) (L : Ideal O) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) :
    (commonEnergy D C hC τ t L W K).re =
      CenteredMomentFirstAllocationGaussEnergy.commonEnergy D C hC τ t L W K := by
  exact (gaussEnergy_hasSum_re Finset.univ
    (sourceGenerator (CenteredMomentFirstSectors.residualPool C hC.1 D.columns))
    (sourceGenerator_supported _) _ W K hK).tsum_eq.symm

lemma original_rawVolume (s : Input ι) (R seed : Ideal O) :
    CenteredMomentFirstAllocationGaussEnergy.rawVolume (original s R seed)=volume s := by
  simp [CenteredMomentFirstAllocationGaussEnergy.rawVolume,original,volume]

lemma allocated_input_columns (s : Input ι) (C R seed L : Ideal O)
    (B : actualAllocations s.pools C) (τ : Character) (t : ℝ) :
    (allocatedData (original s R seed) C L B).columns=
      (original (child s C R B τ t) (R*C) L).columns ∧
    (allocatedData (original s R seed) C L B).beta=
      (original (child s C R B τ t) (R*C) L).beta := by
  have hh := child_columns s C R L B τ t
  simpa only [OriginalData.columns,OriginalData.beta,allocated_pools,allocated_profile,original] using hh

lemma allocated_input_volume (s : Input ι) (C R seed L : Ideal O)
    (B : actualAllocations s.pools C) (τ : Character) (t : ℝ) :
    CenteredMomentFirstAllocationGaussEnergy.rawVolume (allocatedData (original s R seed) C L B)=
      volume (child s C R B τ t) := by
  simp only [CenteredMomentFirstAllocationGaussEnergy.rawVolume,allocatedData,original,
    volume,child,commonData,one_mul,div_mul_div_comm]

lemma allocated_input_energy (s : Input ι) (C R seed L : Ideal O)
    (B : actualAllocations s.pools C) (τ : Character) (t : ℝ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    CenteredMomentFirstAllocationGaussEnergy.allocatedEnergy (original s R seed) C L B τ t W K /
      CenteredMomentFirstAllocationGaussEnergy.rawVolume (allocatedData (original s R seed) C L B)=
      childNormalizedGaussSource s C R L B τ t W K := by
  obtain ⟨hc,hb⟩ := allocated_input_columns s C R seed L B τ t
  unfold CenteredMomentFirstAllocationGaussEnergy.allocatedEnergy
  rw [hc,hb,allocated_input_volume s C R seed L B τ t]
  rfl
