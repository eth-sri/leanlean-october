module
public import OAI.NumberTheory.DirichletL.Moments.SecondCanonicalFrequency

@[expose] public section

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentSecondCanonicalNonunit
open CanonicalQuadraticSieve
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency CenteredMomentCanonicalFirst
open CenteredMomentSecondLedger CenteredMomentPartition CenteredMomentProductCRT

open scoped EisensteinO

section
variable (C D : Ideal O)
include C D

def equalActiveSet  : Finset (CommonIndex C D) :=
  Finset.univ.filter (fun P=>leftExponent C D P=rightExponent C D P ∧ ¬6∣leftExponent C D P)

section
variable (U : Finset (CommonIndex C D))
include U

def nonunitPartitionSet  : Finset (CommonIndex C D) :=
  equalActiveSet C D\U

def nonunitFrequencyGenerator  : O :=
  ∏ P∈nonunitPartitionSet C D U,commonPrime C D P
end


theorem commonPrime_dividedFrequency_iff  (hC : Supported C)
    (w : O) (P : CommonIndex C D) :
    commonPrime C D P∣dividedFrequency (commonPrime C D) (leftExponent C D) (rightExponent C D) w P ↔
      commonPrime C D P∣w := by
  have hc : IsCoprime (commonPrime C D P)
      (cofactor (fun Q=>commonPrime C D Q^min (leftExponent C D Q) (rightExponent C D Q)) P) := by
    unfold cofactor
    apply IsCoprime.prod_right
    intro Q hQ
    exact (commonPrime_coprime C D hC (Finset.mem_erase.mp hQ).1.symm).pow_right
  constructor
  · exact fun h=>hc.dvd_of_dvd_mul_left h
  · exact fun h=>h.trans (dvd_mul_left _ _)

theorem nonunitPartitionSet_eq_actual  (U : Finset (CommonIndex C D))
    (w : O) (hpart : canonicalPartition C D U w) :
    nonunitPartitionSet C D U=actualNonunitSet (commonPrime C D) (leftExponent C D) (rightExponent C D) w := by
  unfold canonicalPartition at hpart
  rw [nonunitPartitionSet,←hpart]
  ext P
  simp only [equalActiveSet,actualUnitSet,actualNonunitSet,Finset.mem_sdiff,Finset.mem_filter,
    Finset.mem_univ,true_and]
  tauto

section
variable (hC : Supported C)
    (U : Finset (CommonIndex C D))
include hC U

theorem nonunitFrequencyGenerator_ne_zero  : nonunitFrequencyGenerator C D U≠0 :=
  Finset.prod_ne_zero_iff.mpr (fun P _=>
    CenteredMomentSupportedCorrelation.supported_element_ne_zero _ (commonPrime_supported C D hC P))

theorem nonunitFrequencyGenerator_dvd  (w : O) (hpart : canonicalPartition C D U w) :
    nonunitFrequencyGenerator C D U∣w := by
  apply Finset.prod_dvd_of_coprime ?_ ?_
  · intro P hP Q hQ hPQ
    exact commonPrime_coprime C D hC hPQ
  · intro P hP
    rw [nonunitPartitionSet_eq_actual C D U w hpart] at hP
    exact (commonPrime_dividedFrequency_iff C D hC w P).mp (Finset.mem_filter.mp hP).2.2.2
end
end







