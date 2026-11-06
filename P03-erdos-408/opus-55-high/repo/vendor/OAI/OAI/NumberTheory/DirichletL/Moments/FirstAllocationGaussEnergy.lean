module

public import OAI.NumberTheory.DirichletL.Moments.FirstPhysicalSourceOriginalData
public import OAI.NumberTheory.DirichletL.Moments.CommonRawScale

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical SchwartzMap

namespace SevenEighths.CenteredMomentFirstAllocationGaussEnergy
open HeckeFamily CanonicalQuadraticSieve CenteredMomentFirstAmplificationChoice
open CenteredMomentFirstPhysicalSource CenteredMomentSourceRow
open CenteredMomentCommonAllocationSum CenteredMomentSourceLiveColumn
open CenteredMomentCommonRawScale CenteredMomentAddedZeroUniform
open CenteredMomentGaussEnergy CenteredMomentSmoothedWindowEnergy
open CenteredMomentOriginalChildEnergy CenteredMomentHeckeColumnWindow
variable {ι : Type*} [Fintype ι]
local instance : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

def commonEnergy (D : OriginalData ι) (C : Ideal ActualEisensteinCubic.O) (hC : Supported C)
    (τ : Character) (t : ℝ) (L : Ideal ActualEisensteinCubic.O) (W : 𝓢(ℝ,ℂ)) (K : ℝ) : ℝ :=
  ∑' z : ActualEisensteinCubic.O, ‖commonGauss D C hC τ t L z‖^2 *
    (W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re

def allocatedEnergy (D : OriginalData ι) (C L : Ideal ActualEisensteinCubic.O)
    (B : actualAllocations D.S C) (τ : Character) (t : ℝ)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) : ℝ :=
  (sourceGaussEnergy (allocatedData D C L B).columns
    (allocatedData D C L B).beta (heightCoeff τ t) W K).re

lemma allocated_hasSum (D : OriginalData ι) (C L : Ideal ActualEisensteinCubic.O)
    (B : actualAllocations D.S C) (τ : Character) (t : ℝ)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) :
    HasSum (fun z : ActualEisensteinCubic.O =>
      ‖gaussPolynomial Finset.univ (sourceGenerator (allocatedData D C L B).columns)
        (sourceGenerator_supported _) (fun I => (allocatedData D C L B).beta I * heightCoeff τ t I) z‖^2 *
      (W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re)
      (allocatedEnergy D C L B τ t W K) :=
  gaussEnergy_hasSum_re _ _ _ _ W K hK

lemma allocated_nonneg (D : OriginalData ι) (C L : Ideal ActualEisensteinCubic.O)
    (B : actualAllocations D.S C) (τ : Character) (t : ℝ)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K)
    (hW : ∀ z : ActualEisensteinCubic.O, 0≤(W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) :
    0≤allocatedEnergy D C L B τ t W K := by
  rw [← (allocated_hasSum D C L B τ t W K hK).tsum_eq]
  exact tsum_nonneg (fun z => mul_nonneg (sq_nonneg _) (hW z))

theorem common_energy_allocation (D : OriginalData ι)
    (hS : ∀ i, ∀ I∈D.S i, I≠0) (hp : ∀ i, ∀ I∈D.S (Sum.inl i), Prime I)
    (C : Ideal ActualEisensteinCubic.O) (hC : Supported C) (hseed : D.s∣C)
    (τ : Character) (t : ℝ) (L : Ideal ActualEisensteinCubic.O) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K)
    (hW : ∀ z : ActualEisensteinCubic.O, 0≤(W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) :
    commonEnergy D C hC τ t L W K ≤
      ((actualAllocations D.S C).card:ℝ) * ∑ B : actualAllocations D.S C,
        ‖frozenCoefficient B.val C D.R D.nu D.slot D.lengths‖^2 * allocatedEnergy D C L B τ t W K := by
  unfold commonEnergy
  apply Real.tsum_le_of_sum_le (fun z => mul_nonneg (sq_nonneg _) (hW z))
  intro rows
  calc
    _ ≤ ∑ z∈rows, ((actualAllocations D.S C).card:ℝ) * ∑ B : actualAllocations D.S C,
        ‖frozenCoefficient B.val C D.R D.nu D.slot D.lengths‖^2 *
          (‖gaussPolynomial Finset.univ (sourceGenerator (allocatedData D C L B).columns)
            (sourceGenerator_supported _) (fun I => (allocatedData D C L B).beta I * heightCoeff τ t I) z‖^2 *
          (W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) := by
      apply Finset.sum_le_sum
      intro z hz
      rw [common_gauss_allocation D hS hp C hC hseed τ t L z]
      have hc := mul_le_mul_of_nonneg_right
        (CubicEisenstein.norm_sum_sq_le_card Finset.univ
          (fun B : actualAllocations D.S C =>
            frozenCoefficient B.val C D.R D.nu D.slot D.lengths *
              gaussPolynomial Finset.univ (sourceGenerator (allocatedData D C L B).columns)
                (sourceGenerator_supported _) (fun I => (allocatedData D C L B).beta I * heightCoeff τ t I) z))
        (hW z)
      simpa only [Finset.card_univ,Fintype.card_coe,norm_mul,mul_pow,Finset.sum_mul,mul_assoc] using hc
    _ = ((actualAllocations D.S C).card:ℝ) * ∑ B : actualAllocations D.S C,
        ‖frozenCoefficient B.val C D.R D.nu D.slot D.lengths‖^2 *
          ∑ z∈rows, ‖gaussPolynomial Finset.univ (sourceGenerator (allocatedData D C L B).columns)
            (sourceGenerator_supported _) (fun I => (allocatedData D C L B).beta I * heightCoeff τ t I) z‖^2 *
            (W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re := by
      rw [← Finset.mul_sum,Finset.sum_comm]
      simp only [Finset.mul_sum]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply Finset.sum_le_sum
      intro B hB
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      exact sum_le_hasSum rows (fun z _ => mul_nonneg (sq_nonneg _) (hW z))
        (allocated_hasSum D C L B τ t W K hK)

def rawVolume (D : OriginalData ι) : ℝ :=
  (D.X₁*D.X₂/((Ideal.absNorm D.B₁:ℝ)*Ideal.absNorm D.B₂)) * ∏ i,D.lengths i

lemma rawVolume_pos (D : OriginalData ι) (hX₁ : 0<D.X₁) (hX₂ : 0<D.X₂)
    (hB₁ : D.B₁≠0) (hB₂ : D.B₂≠0) (hP : ∀ i,0<D.lengths i) : 0<rawVolume D := by
  apply mul_pos (div_pos (by positivity) _)
    (Finset.prod_pos (by grind))
  exact mul_pos (CenteredMomentFirstScale.norm_pos _ hB₁) (CenteredMomentFirstScale.norm_pos _ hB₂)

lemma allocated_rawVolume_mul (D : OriginalData ι) (C L : Ideal ActualEisensteinCubic.O)
    (B : actualAllocations D.S C) (hB₁ : D.B₁≠0) (hB₂ : D.B₂≠0) :
    rawVolume (allocatedData D C L B) * rawReduction B.val D.lengths = rawVolume D := by
  have hB := (allocation_data D.S C B.val (Finset.mem_filter.mp B.property).1).1
  have hv := remainingRaw_source B.val hB D.B₁ D.B₂ hB₁ hB₂ (D.X₁*D.X₂) D.lengths
  change _ = rawVolume (allocatedData D C L B) at hv
  rw [← hv]
  exact raw_scale_identity B.val hB _ D.lengths

lemma allocated_rawVolume (D : OriginalData ι) (C L : Ideal ActualEisensteinCubic.O)
    (B : actualAllocations D.S C) (hB₁ : D.B₁≠0) (hB₂ : D.B₂≠0)
    (hP : ∀ i,0<D.lengths i) :
    rawVolume (allocatedData D C L B) = rawVolume D / rawReduction B.val D.lengths := by
  have hr := rawReduction_pos B.val
    (allocation_data D.S C B.val (Finset.mem_filter.mp B.property).1).1 D.lengths hP
  exact (eq_div_iff hr.ne').mpr (allocated_rawVolume_mul D C L B hB₁ hB₂)

def frozenControl (B : Tuple ι) (M : ι → ℝ) : ℝ :=
  ∏ i∈Finset.univ.filter (fun i => B (Sum.inl i)≠1),M i

lemma frozen_norm_bound (D : OriginalData ι) (C : Ideal ActualEisensteinCubic.O)
    (B : actualAllocations D.S C) (M : ι → ℝ) (_hM : ∀ i,0≤M i)
    (hν : ∀ i I,‖D.nu i I‖≤1) (hW : ∀ i x,‖D.slot i x‖≤M i) :
    ‖frozenCoefficient B.val C D.R D.nu D.slot D.lengths‖≤frozenControl B.val M := by
  unfold frozenCoefficient frozenControl
  rw [norm_mul]
  have hc : ‖(if IsCoprime C D.R then (1:ℂ) else 0)‖≤1 := by split_ifs <;> simp
  apply (mul_le_of_le_one_right (norm_nonneg _) hc).trans
  rw [norm_prod]
  apply Finset.prod_le_prod₀ (by grind)
  intro i hi
  rw [norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) (by grind)).trans (by grind)

theorem frozen_normalized_bound (N : ℕ) (a b : ℝ) (ha : 0<a)
    (D : OriginalData ι) (hcard : Fintype.card ι≤N)
    (C : Ideal ActualEisensteinCubic.O) (hC : C≠0) (B : actualAllocations D.S C)
    (M : ι → ℝ) (hM : ∀ i,0≤M i) (hP : ∀ i,0<D.lengths i)
    (hν : ∀ i I,‖D.nu i I‖≤1) (hWnorm : ∀ i x,‖D.slot i x‖≤M i)
    (hW : ∀ i,Function.support (D.slot i)⊆Set.Icc a b) :
    ‖frozenCoefficient B.val C D.R D.nu D.slot D.lengths‖^2/rawReduction B.val D.lengths ≤
      (max 1 b)^N/(Ideal.absNorm C:ℝ)*(frozenControl B.val M)^2 := by
  have hB := (allocation_data D.S C B.val (Finset.mem_filter.mp B.property).1).1
  have hR := rawReduction_pos B.val hB D.lengths hP
  have hN := CenteredMomentFirstScale.norm_pos C hC
  by_cases hz : frozenCoefficient B.val C D.R D.nu D.slot D.lengths=0
  · rw [hz,norm_zero,zero_pow (by positivity),zero_div]
    positivity
  · have hm := frozen_norm_bound D C B M hM hν hWnorm
    have hh := (actual_reduction_norm B.val hB C D.R
      (Finset.mem_filter.mp B.property).2 D.nu D.slot D.lengths hP a b ha hW hz).2
    have he : (max 1 b)^Fintype.card ι≤(max 1 b)^N :=
      pow_le_pow_right₀ (by simp) hcard
    have hi : (1:ℝ)/rawReduction B.val D.lengths ≤ (max 1 b)^N/(Ideal.absNorm C:ℝ) := by
      apply (div_le_div_iff₀ hR hN).mpr
      simpa only [one_mul] using hh.trans (mul_le_mul_of_nonneg_right he hR.le)
    calc
      _ ≤ (frozenControl B.val M)^2/rawReduction B.val D.lengths :=
        div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hm _) hR.le
      _ = (frozenControl B.val M)^2*(1/rawReduction B.val D.lengths) := by ring
      _ ≤ (frozenControl B.val M)^2*((max 1 b)^N/(Ideal.absNorm C:ℝ)) :=
        mul_le_mul_of_nonneg_left hi (sq_nonneg _)
      _ = _ := by ring

theorem normalized_common_energy_allocation (D : OriginalData ι)
    (hS : ∀ i,∀ I∈D.S i,I≠0) (hp : ∀ i,∀ I∈D.S (Sum.inl i),Prime I)
    (C : Ideal ActualEisensteinCubic.O) (hC : Supported C) (hseed : D.s∣C)
    (τ : Character) (t : ℝ) (L : Ideal ActualEisensteinCubic.O) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K)
    (hW : ∀ z : ActualEisensteinCubic.O,0≤(W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re)
    (hX₁ : 0<D.X₁) (hX₂ : 0<D.X₂) (hB₁ : D.B₁≠0) (hB₂ : D.B₂≠0)
    (hP : ∀ i,0<D.lengths i) :
    commonEnergy D C hC τ t L W K / rawVolume D ≤
      ((actualAllocations D.S C).card:ℝ) * ∑ B : actualAllocations D.S C,
        (‖frozenCoefficient B.val C D.R D.nu D.slot D.lengths‖^2/rawReduction B.val D.lengths) *
          (allocatedEnergy D C L B τ t W K/rawVolume (allocatedData D C L B)) := by
  have hV := rawVolume_pos D hX₁ hX₂ hB₁ hB₂ hP
  have he := div_le_div_of_nonneg_right
    (common_energy_allocation D hS hp C hC hseed τ t L W K hK hW) hV.le
  apply he.trans_eq
  rw [mul_div_assoc,Finset.sum_div]
  apply congrArg (fun x : ℝ => ((actualAllocations D.S C).card:ℝ)*x)
  apply Finset.sum_congr rfl
  intro B hB
  have hR := rawReduction_pos B.val
    (allocation_data D.S C B.val (Finset.mem_filter.mp B.property).1).1 D.lengths hP
  rw [allocated_rawVolume D C L B hB₁ hB₂ hP]
  field_simp

end SevenEighths.CenteredMomentFirstAllocationGaussEnergy

end

end OAI
