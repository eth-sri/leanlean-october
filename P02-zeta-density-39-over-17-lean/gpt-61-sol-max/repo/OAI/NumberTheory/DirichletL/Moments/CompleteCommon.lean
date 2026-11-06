module
public import OAI.NumberTheory.DirichletL.Moments.Support
public import OAI.NumberTheory.DirichletL.Moments.RankinRadical
public import OAI.NumberTheory.DirichletL.CenteredExceptionalCount

@[expose] public section

namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentCompleteCommon
open IdealMobiusDivisorSum CenteredMomentSupport
open CenteredExceptionalCount CenteredMomentRankinRadical CanonicalQuadraticSieve
open scoped EisensteinO

section
variable (I J : Ideal O)
include I J

def commonSupport  : Finset (Ideal O) := primeSupport I ∩ primeSupport J

def commonPart  : Ideal O :=
  ∏ P ∈ commonSupport I J, P ^ valuation I P

def residualPart  : Ideal O :=
  ∏ P ∈ primeSupport I \ primeSupport J, P ^ valuation I P

theorem commonSupport_comm  : commonSupport I J = commonSupport J I :=
  Finset.inter_comm _ _
end


section
variable (I : Ideal O) (S : Finset (Ideal O))
include I S

theorem supportExtract_eq_power_product  :
    supportExtract I S = ∏ P ∈ primeSupport I ∩ S, P ^ valuation I P := by
  unfold supportExtract
  rw [Finset.prod_multiset_count_of_subset _ (primeSupport I ∩ S) (by
    intro P hP
    exact Finset.mem_inter.mpr ⟨Multiset.mem_toFinset.mpr (Multiset.mem_filter.mp
      (Multiset.mem_toFinset.mp hP)).1, (Multiset.mem_filter.mp
      (Multiset.mem_toFinset.mp hP)).2⟩)]
  apply Finset.prod_congr rfl
  intro P hP
  simp only [Multiset.count_filter, (Finset.mem_inter.mp hP).2, ↓reduceIte]
  rfl

theorem supportResidual_eq_power_product  :
    supportResidual I S = ∏ P ∈ primeSupport I \ S, P ^ valuation I P := by
  unfold supportResidual
  rw [Finset.prod_multiset_count_of_subset _ (primeSupport I \ S) (by
    intro P hP
    exact Finset.mem_sdiff.mpr ⟨Multiset.mem_toFinset.mpr (Multiset.mem_filter.mp
      (Multiset.mem_toFinset.mp hP)).1, (Multiset.mem_filter.mp
      (Multiset.mem_toFinset.mp hP)).2⟩)]
  apply Finset.prod_congr rfl
  intro P hP
  simp only [Multiset.count_filter, (Finset.mem_sdiff.mp hP).2]
  rfl
end


section
variable (I J : Ideal O)
include I J

theorem commonPart_eq_supportExtract  :
    commonPart I J = supportExtract I (commonSupport I J) := by
  rw [supportExtract_eq_power_product]
  simp only [commonPart, commonSupport, ← Finset.inter_assoc, Finset.inter_self]

theorem residualPart_eq_supportResidual  :
    residualPart I J = supportResidual I (commonSupport I J) := by
  rw [supportResidual_eq_power_product]
  have he : primeSupport I \ commonSupport I J = primeSupport I \ primeSupport J := by
    ext P
    simp only [Finset.mem_sdiff, commonSupport, Finset.mem_inter]
    tauto
  rw [he]
  rfl

theorem commonPart_ne_zero  : commonPart I J ≠ 0 := by
  rw [commonPart_eq_supportExtract]
  exact supportExtract_ne_zero _ _

theorem residualPart_ne_zero  : residualPart I J ≠ 0 := by
  rw [residualPart_eq_supportResidual]
  exact supportResidual_ne_zero _ _

theorem reconstruct  (hI : I ≠ 0) :
    I = commonPart I J * residualPart I J := by
  rw [commonPart_eq_supportExtract, residualPart_eq_supportResidual]
  exact (support_reconstruct I hI _).symm

theorem commonPart_support  :
    primeSupport (commonPart I J) = commonSupport I J := by
  rw [commonPart_eq_supportExtract, supportExtract_support]
  simp only [commonSupport, ← Finset.inter_assoc, Finset.inter_self]

theorem commonParts_equal_support  :
    primeSupport (commonPart I J) = primeSupport (commonPart J I) := by
  rw [commonPart_support, commonPart_support, commonSupport_comm I J]
end


theorem commonPart_valuation (I J P : Ideal O) :
    valuation (commonPart I J) P = if P ∈ commonSupport I J then valuation I P else 0 := by
  rw [commonPart_eq_supportExtract]
  exact supportExtract_count I P _

section
variable (I J : Ideal O)
include I J

theorem commonPart_residualPart_coprime  :
    IsCoprime (commonPart I J) (residualPart J I) := by
  rw [commonPart_eq_supportExtract, residualPart_eq_supportResidual, ← commonSupport_comm I J]
  exact extracted_residual_coprime I J _

theorem commonPart_own_residual_coprime  :
    IsCoprime (commonPart I J) (residualPart I J) := by
  rw [commonPart_eq_supportExtract, residualPart_eq_supportResidual]
  exact extracted_residual_coprime I I _

theorem residualParts_coprime  :
    IsCoprime (residualPart I J) (residualPart J I) := by
  rw [residualPart_eq_supportResidual, residualPart_eq_supportResidual, ← commonSupport_comm I J]
  exact common_support_residual_coprime I J

theorem commonPart_dvd  (hI : I ≠ 0) : commonPart I J ∣ I :=
  ⟨residualPart I J, reconstruct I J hI⟩

theorem commonRadical_dvd_commonPart  : commonRadical I J ∣ commonPart I J := by
  apply support_product_dvd (commonPart_ne_zero I J)
  rw [commonPart_support]
  exact Finset.Subset.refl _

section
variable (hI : Supported I)
include hI

theorem commonPart_supported  : Supported (commonPart I J) := by
  rw [commonPart_eq_supportExtract]
  exact supportExtract_supported I hI _

theorem residualPart_supported  : Supported (residualPart I J) := by
  rw [residualPart_eq_supportResidual]
  exact supportResidual_supported I hI _
end
end


theorem common_valuations_pos (I J P : Ideal O) (hP : P ∈ commonSupport I J) :
    0 < valuation I P ∧ 0 < valuation J P := by
  obtain ⟨hI, hJ⟩ := Finset.mem_inter.mp hP
  exact ⟨Multiset.count_pos.mpr (Multiset.mem_toFinset.mp hI),
    Multiset.count_pos.mpr (Multiset.mem_toFinset.mp hJ)⟩

section
variable (I : Ideal O)
include I

theorem residualPart_self  : residualPart I I = 1 := by
  simp only [residualPart, Finset.sdiff_self, Finset.prod_empty]

theorem commonPart_self  (hI : I ≠ 0) : commonPart I I = I := by
  have h := reconstruct I I hI
  rw [residualPart_self, mul_one] at h
  exact h.symm
end


section
variable (I J : Ideal O) (hI : I ≠ 0)
include I J hI

theorem absNorm_reconstruct  :
    Ideal.absNorm I = Ideal.absNorm (commonPart I J) * Ideal.absNorm (residualPart I J) := by
  have h := congrArg Ideal.absNorm (reconstruct I J hI)
  simpa only [map_mul] using h

theorem absNorm_commonPart_le  :
    Ideal.absNorm (commonPart I J) ≤ Ideal.absNorm I :=
  Nat.le_of_dvd (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI))
    (map_dvd Ideal.absNorm (commonPart_dvd I J hI))
end







