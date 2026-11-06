module
public import OAI.NumberTheory.DirichletL.Moments.SecondSixthReduction
import WeylPort.Analytic.RealLaplace

@[expose] public section

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentSecondSixthSource
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondCanonicalLedger CenteredMomentSecondMovingSupport CenteredMomentSecondSixthReduction
open CenteredMomentCanonicalFirst
local notation "O" => ActualEisensteinCubic.O

section
variable (C D : Ideal O)
include C D
theorem sixthFactor_span_dvd (hC : Supported C)
    (hCD : primeSupport C=primeSupport D) (U : Finset (CommonIndex C D)) :
    Ideal.span {sixthFactor C D U}∣C := by
  conv_rhs => rw [←left_ideal_product C D hC hCD]
  pm_6455
  have hc := leftExponent_pos C D P
  have hm : min (leftExponent C D P) (rightExponent C D P)≤leftExponent C D P := min_le_left _ _
  unfold fixedExponent
  grind

theorem fixed_sixth_coefficient (U : Finset (CommonIndex C D))
    (I : Ideal O) (hI : Supported I) :
    idealRowHom (commonFrequencyGenerator C D *nonunitFrequencyGenerator C D U) I =
      idealRowHom (reducedNumerator C D U) I *
        (if IsCoprime I (Ideal.span {sixthFactor C D U}) then 1 else 0) := by
  rw [fixed_sixth_factorization,idealRowHom_argument_mul,idealRowHom_sixth_mask _ I hI]

theorem residual_sixth_coefficient (hC : Supported C)
    (hCD : primeSupport C=primeSupport D) (U : Finset (CommonIndex C D))
    (I : Ideal O) (hI : Supported I) (hcop : IsCoprime C I) :
    idealRowHom (commonFrequencyGenerator C D *nonunitFrequencyGenerator C D U) I =
      idealRowHom (reducedNumerator C D U) I := by
  rw [fixed_sixth_coefficient C D U I hI,ite_eq_left
    (hcop.symm.of_isCoprime_of_dvd_right (sixthFactor_span_dvd C D hC hCD U)),mul_one]
end

abbrev ActiveIndex (C D : Ideal O) (U : Finset (CommonIndex C D)) := ↥(fixedActiveSet C D U)

def activePrime (C D : Ideal O) (U : Finset (CommonIndex C D))
    (P : ActiveIndex C D U) : O := commonPrime C D P.val

def activeExponent (C D : Ideal O) (U : Finset (CommonIndex C D))
    (P : ActiveIndex C D U) : ℕ := fixedExponent C D U P.val%6

section
variable (C D : Ideal O) (U : Finset (CommonIndex C D))
include C D U
theorem activeExponent_pos
    (P : ActiveIndex C D U) : 0<activeExponent C D U P := by
  have hp : ¬6∣fixedExponent C D U P.val := (Finset.mem_filter.mp P.property).2
  exact Nat.pos_of_ne_zero (fun h=>hp (Nat.dvd_of_mod_eq_zero h))

theorem reducedNumerator_active_product :
    reducedNumerator C D U=∏ P : ActiveIndex C D U,activePrime C D U P^activeExponent C D U P := by
  simp only [activePrime,activeExponent]
  rw [Finset.prod_coe_sort (fixedActiveSet C D U)
    (fun P : CommonIndex C D =>commonPrime C D P^(fixedExponent C D U P%6))]
  unfold reducedNumerator
  symm
  apply Finset.prod_subset (Finset.subset_univ _)
  intro P hP hn
  have hp : 6∣fixedExponent C D U P := by
    pm_124 fixedActiveSet Finset.mem_filter Finset.mem_univ true_and not_not hn
  simp only [Nat.mod_eq_zero_of_dvd hp,pow_zero]
end

end SevenEighths.CenteredMomentSecondSixthSource

end

end OAI
