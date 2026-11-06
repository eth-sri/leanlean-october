module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Moments.SecondCanonicalFrequency

@[expose] public section

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentSecondCanonicalNonunit
open CanonicalQuadraticSieve CompletedGauss ConcretePrimeRowBridge
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency CenteredMomentCanonicalFirst
open CenteredMomentSecondLedger CenteredMomentPartition CenteredMomentProductCRT
open CenteredMomentSupport


def equalActiveSet (C D )  :=
  Finset.univ.filter (fun P=>leftExponent C D P=rightExponent C D P ∧ ¬6∣leftExponent C D P)

def nonunitPartitionSet (C D ) (U : Finset (CommonIndex C D))  :=
  equalActiveSet C D\U

def nonunitFrequencyGenerator (C D ) (U : Finset (CommonIndex C D))  :=
  ∏ P∈nonunitPartitionSet C D U,commonPrime C D P

theorem commonPrime_dividedFrequency_iff  C D  (hC : Supported C)
     w   P  :
    commonPrime C D P∣dividedFrequency (commonPrime C D) (leftExponent C D) (rightExponent C D) w P ↔
      commonPrime C D P∣w := { mp := IsCoprime.dvd_of_dvd_mul_left (IsCoprime.prod_right fun Q hQ => IsCoprime.pow_right (OAI.SevenEighths.CenteredMomentSecondCanonical.commonPrime_coprime C D hC (Ne.symm (Finset.mem_erase.mp hQ).left))), mpr := fun h => Dvd.dvd.trans h (dvd_mul_left w (OAI.SevenEighths.CenteredMomentProductCRT.cofactor (fun j => OAI.SevenEighths.CenteredMomentSecondCanonical.commonPrime C D j ^ Min.min (OAI.SevenEighths.CenteredMomentCanonicalFirst.leftExponent C D j) (OAI.SevenEighths.CenteredMomentCanonicalFirst.rightExponent C D j)) P)) }

theorem nonunitPartitionSet_eq_actual  C D   U 
     w  (hpart : canonicalPartition C D U w) :
    nonunitPartitionSet C D U=actualNonunitSet (commonPrime C D) (leftExponent C D) (rightExponent C D) w := by
  grind [canonicalPartition, nonunitPartitionSet, equalActiveSet, actualUnitSet, actualNonunitSet]

theorem nonunitFrequencyGenerator_ne_zero  C D  (hC : Supported C)
     U  : nonunitFrequencyGenerator C D U≠0 :=
  Finset.prod_ne_zero_iff.mpr (fun P _=>
    CenteredMomentSupportedCorrelation.supported_element_ne_zero _ (commonPrime_supported C D hC P))

theorem nonunitFrequencyGenerator_dvd  C D  (hC : Supported C)
     U   w  (hpart : canonicalPartition C D U w) :
    nonunitFrequencyGenerator C D U∣w := by
  apply Finset.prod_dvd_of_coprime ?_ ?_
  · intro P hP Q hQ hPQ
    exact commonPrime_coprime C D hC hPQ
  · intro P hP
    rw [nonunitPartitionSet_eq_actual C D U w hpart] at hP
    exact (commonPrime_dividedFrequency_iff C D hC w P).mp (Finset.mem_filter.mp hP).2.2.2

end SevenEighths.CenteredMomentSecondCanonicalNonunit

end

end OAI
