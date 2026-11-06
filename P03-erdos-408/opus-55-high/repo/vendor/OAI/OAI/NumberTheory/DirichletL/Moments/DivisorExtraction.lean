module

public import OAI.NumberTheory.DirichletL.Moments.DivisorAllocation

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.CenteredMomentDivisorExtraction
open IdealMobiusDivisorSum CenteredMomentDivisorAllocation
variable {ι : Type*} [DecidableEq ι]

def selectedPrimes (D : Ideal ActualEisensteinCubic.O) (s : Finset ι) (a : Allocation D s) (i : ι) :
    Finset (primeSupport D) := Finset.univ.filter (fun P => i ∈ (a P).val)

def selectedDivisor (D : Ideal ActualEisensteinCubic.O) (s : Finset ι) (a : Allocation D s) (i : ι) : Ideal ActualEisensteinCubic.O :=
  ∏ P ∈ selectedPrimes D s a i, (P:Ideal ActualEisensteinCubic.O)

theorem selected_divides_factor (D : Ideal ActualEisensteinCubic.O) (s : Finset ι) (v : ι → Ideal ActualEisensteinCubic.O)
    (a : Allocation D s) (hn : allocationTerm D s v a ≠ 0)
    (P : primeSupport D) (i : ι) (hi : i ∈ (a P).val) : (P:Ideal ActualEisensteinCubic.O)∣v i := by
  have hP := (Finset.prod_ne_zero_iff.mp hn) P (Finset.mem_univ P)
  have hprod := (mul_ne_zero_iff.mp hP).2
  have hfactor := (Finset.prod_ne_zero_iff.mp hprod) i hi
  simp_all

theorem selectedDivisor_ne_zero (D : Ideal ActualEisensteinCubic.O) (s : Finset ι) (a : Allocation D s) (i : ι) :
    selectedDivisor D s a i ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr (fun P _ => (support_prime P.property).ne_zero)

theorem selectedDivisor_dvd (D : Ideal ActualEisensteinCubic.O) (s : Finset ι) (v : ι → Ideal ActualEisensteinCubic.O)
    (a : Allocation D s) (hn : allocationTerm D s v a ≠ 0) (i : ι) :
    selectedDivisor D s a i ∣ v i := by
  apply Finset.prod_dvd_of_coprime ?_ ?_
  · intro P hP Q hQ hne
    let : (P:Ideal ActualEisensteinCubic.O).IsMaximal := (Ideal.isPrime_of_prime (support_prime P.property)).isMaximal
      (support_prime P.property).ne_zero
    let : (Q:Ideal ActualEisensteinCubic.O).IsMaximal := (Ideal.isPrime_of_prime (support_prime Q.property)).isMaximal
      (support_prime Q.property).ne_zero
    exact Ideal.isCoprime_of_isMaximal (by grind)
  · intro P hP
    exact selected_divides_factor D s v a hn P i (Finset.mem_filter.mp hP).2

end SevenEighths.CenteredMomentDivisorExtraction

end

end OAI
