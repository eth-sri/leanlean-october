module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Moments.CommonAllowance
public import OAI.NumberTheory.DirichletL.Moments.SecondCanonical
public import OAI.NumberTheory.DirichletL.Moments.FirstCanonicalFamily

@[expose] public section

namespace OAI


open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentFirstCanonicalAllowance
open ActualEisensteinCubic CanonicalQuadraticSieve ConcreteTraceCRT
open CenteredMomentActive CenteredMomentCanonicalFirst CenteredMomentCompleteCommon
open CenteredMomentSecondCanonical CenteredMomentFirstCanonicalFamily
open CenteredMomentRankinRadical CenteredMomentCommonAllowance


theorem activeConductor_span_product  I J  :
    Ideal.span {activeConductor I J} =
      ∏ P ∈ activeSupport (Finset.univ : Finset (CommonIndex I J))
        (leftExponent I J) (rightExponent I J), P.val := by
  rw [activeConductor, span_finitePrimeModulus]
  exact Finset.prod_coe_sort (s := ActiveIndex I J)
    (f := fun P : CommonIndex I J => P.val)

theorem active_generator_ideal_product  I J  (hI : Supported I) :
    (∏ P ∈ activeSupport (Finset.univ : Finset (CommonIndex I J))
      (leftExponent I J) (rightExponent I J), Ideal.span {commonPrime I J P}) =
      Ideal.span {activeConductor I J} := by
  simp_rw [commonPrime_span I J hI]
  exact (activeConductor_span_product I J).symm

theorem common_ideal_product  I J  :
    (∏ P : CommonIndex I J, P.val) = commonRadical I J := Finset.prod_coe_sort (OAI.SevenEighths.CenteredMomentCompleteCommon.commonSupport I J) fun P => P

theorem common_generator_ideal_product  I J  (hI : Supported I) :
    (∏ P : CommonIndex I J, Ideal.span {commonPrime I J P}) = commonRadical I J := by
  simp_rw [commonPrime_span I J hI]
  exact common_ideal_product I J

theorem actual_canonical_common_support_allowance
     C D  (hC : Supported C) (hD : Supported D)
    (hCD : CompletedGauss.primeSupport C = CompletedGauss.primeSupport D)
     Z  (hZ : 1 < Z) :
    let c := Real.logb Z (C.absNorm : ℝ)
    let d := Real.logb Z (D.absNorm : ℝ)
    let p := Real.logb Z ((commonRadical C D).absNorm : ℝ)
    let r := Real.logb Z ((Ideal.span {activeConductor C D}).absNorm : ℝ)
    max (3*c-5*d-r) 0/6 + max (3*d-5*c-r) 0/6 ≤ c+d-2*p-r := by
  have h := actual_common_support_allowance (commonPrime C D)
    (commonPrime_supported C D hC) (leftExponent C D) (rightExponent C D)
    (leftExponent_pos C D) (rightExponent_pos C D) Z hZ
  dsimp only at h ⊢
  rw [left_ideal_product C D hC hCD, right_ideal_product C D hC hD hCD,
    common_generator_ideal_product C D hC, active_generator_ideal_product C D hC] at h
  exact h

theorem activeConductor_span_filter  I J  :
    Ideal.span {activeConductor I J} =
      ∏ P ∈ (commonSupport I J).filter (fun P =>
        netExponent (CenteredExceptionalCount.valuation I P)
          (CenteredExceptionalCount.valuation J P) ≠ 0), P := by
  rw [activeConductor_span_product]
  simp only [CenteredMomentActive.activeSupport, Finset.prod_filter]
  exact Finset.prod_coe_sort (s := commonSupport I J)
    (f := fun P : Ideal ActualEisensteinCubic.O => if netExponent (CenteredExceptionalCount.valuation I P)
      (CenteredExceptionalCount.valuation J P) ≠ 0 then P else 1)

end SevenEighths.CenteredMomentFirstCanonicalAllowance



end OAI
