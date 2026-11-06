module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Moments.SecondSourceFrequency

@[expose] public section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSecondRetainedRows
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ConcretePrimeRowBridge
open CenteredMomentSecondSectorFrequency CenteredMomentSecondSectorRetained CenteredMomentSectorLocalization
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentCanonicalFirst


def retainedRows (R : ℝ) (A : ActualEisensteinCubic.O)  := rowNormDisk (Nat.ceil (4*R/normValue A))

section
variable (η : Character) (t : ℝ) (S : Finset (Ideal ActualEisensteinCubic.O)) (β : Ideal ActualEisensteinCubic.O→ℂ) (C D : Ideal ActualEisensteinCubic.O) (hC : Supported C) (hD : Supported D) (U : Finset (CommonIndex C D)) (W : 𝓢(ℝ,ℂ)) (K R : ℝ) (A h : ActualEisensteinCubic.O) (hA : A≠0)

include hA in
theorem retained_mem_rows      
    (hh : retainedWeight R (normValue (A*h))≠0) : h∈retainedRows R A := by
  have he := retainedWeight_enclosure R _ hh
  have hAh : A*h≠0 := by
    intro hz
    have hn : normValue (A*h)=0 := by simp [hz,normValue]
    linarith [he.1]
  have hh0 : h≠0 := right_ne_zero_of_mul hAh
  apply mem_rowNormDisk.mpr
  constructor
  · simp_all
  · have hbound : normValue h≤4*R/normValue A := by
      apply (le_div_iff₀ (normValue_pos A hA)).mpr
      simpa only [normValue_mul,mul_comm] using he.2
    have hb := hbound.trans (Nat.le_ceil (4*R/normValue A))
    unfold normValue at hb
    exact_mod_cast hb

theorem physical_sector_zero_of_weight    
             
         j 
    (hj : retainedWeight R (normValue j)=0) :
    sectorFrequency η t S β C D hC hD (physicalKernel C D W K R) j=0 := by
  simp only [sectorFrequency,physicalKernel,hj,Complex.ofReal_zero,mul_zero,zero_mul,Finset.sum_const_zero]

include hA in
theorem physical_partition_finite_rows    
             
            (part : ActualEisensteinCubic.O→Prop) :
    (∑' h : ActualEisensteinCubic.O,if part h then
      sectorFrequency η t S β C D hC hD (physicalKernel C D W K R) (A*h) else 0)=
      ∑ h∈retainedRows R A,if part h then
        sectorFrequency η t S β C D hC hD (physicalKernel C D W K R) (A*h) else 0 := by
  apply tsum_eq_sum
  grind [physical_sector_zero_of_weight, retained_mem_rows]

include η t S β hC hD U W K R in
theorem actual_GV_finite_rows    
             
          :
    let A := commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U
    (∑' h : ActualEisensteinCubic.O,if canonicalPartition C D U (nonunitFrequencyGenerator C D U*h) then
      sectorFrequency η t S β C D hC hD (physicalKernel C D W K R) (A*h) else 0)=
      ∑ h∈retainedRows R A,if canonicalPartition C D U (nonunitFrequencyGenerator C D U*h) then
        sectorFrequency η t S β C D hC hD (physicalKernel C D W K R) (A*h) else 0 := by
  dsimp only
  exact physical_partition_finite_rows η t S β C D hC hD W K R _
    (mul_ne_zero (commonFrequencyGenerator_ne_zero C D hC)
      (nonunitFrequencyGenerator_ne_zero C D hC U)) _

end

end SevenEighths.CenteredMomentSecondRetainedRows

end

end OAI
