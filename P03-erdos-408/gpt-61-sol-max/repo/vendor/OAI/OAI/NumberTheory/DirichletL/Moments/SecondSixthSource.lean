module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Moments.SecondSixthReduction

@[expose] public section

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentSecondSixthSource
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondCanonicalLedger CenteredMomentSecondMovingSupport CenteredMomentSecondSixthReduction
open CenteredMomentCanonicalFirst


theorem sixthFactor_span_dvd  C D  (hC : Supported C)
    (hCD : primeSupport C=primeSupport D)  U  :
    Ideal.span {sixthFactor C D U}∣C := by
  conv_rhs => rw [←left_ideal_product C D hC hCD]
  simp only [sixthFactor,span_finset_product,←Ideal.span_singleton_pow]
  apply Finset.prod_dvd_prod_of_dvd
  intro P hP
  apply pow_dvd_pow
  grind [min, leftExponent, rightExponent, fixedExponent]

theorem fixed_sixth_coefficient  C D   U 
     I  (hI : Supported I) :
    idealRowHom (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) I=
      idealRowHom (reducedNumerator C D U) I*
        (if IsCoprime I (Ideal.span {sixthFactor C D U}) then 1 else 0) := by
  rw [fixed_sixth_factorization,idealRowHom_argument_mul,idealRowHom_sixth_mask _ I hI]

theorem residual_sixth_coefficient  C D  (hC : Supported C)
    (hCD : primeSupport C=primeSupport D)  U 
     I  (hI : Supported I) (hcop : IsCoprime C I) :
    idealRowHom (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) I=
      idealRowHom (reducedNumerator C D U) I := by
  rw [fixed_sixth_coefficient C D U I hI,ite_eq_left
    (hcop.symm.of_isCoprime_of_dvd_right (sixthFactor_span_dvd C D hC hCD U)),mul_one]

abbrev ActiveIndex (C D ) (U ) := ↥(fixedActiveSet C D U)

def activePrime (C D ) (U )
    (P : ActiveIndex C D U)  := commonPrime C D P.val

def activeExponent (C D ) (U )
    (P : ActiveIndex C D U)  := fixedExponent C D U P.val%6

theorem activeExponent_pos  C D   U 
     P  : 0<activeExponent C D U P := Nat.pos_of_ne_zero fun h => (Finset.mem_filter.mp P.property).right (Nat.dvd_of_mod_eq_zero h)

theorem reducedNumerator_active_product  C D   U  :
    reducedNumerator C D U=∏ P : ActiveIndex C D U,activePrime C D U P^activeExponent C D U P := by
  simp only [activePrime,activeExponent]
  rw [Finset.prod_coe_sort (fixedActiveSet C D U)
    (fun P : CommonIndex C D=>commonPrime C D P^(fixedExponent C D U P%6))]
  unfold reducedNumerator
  symm
  apply Finset.prod_subset (Finset.subset_univ _)
  intro P hP hn
  have hp : 6∣fixedExponent C D U P := by
    simpa only [fixedActiveSet,Finset.mem_filter,Finset.mem_univ,true_and,not_not] using hn
  simp only [Nat.mod_eq_zero_of_dvd hp,pow_zero]

end SevenEighths.CenteredMomentSecondSixthSource

end

end OAI
