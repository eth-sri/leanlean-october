module

public import OAI.NumberTheory.DirichletL.Reflection.MarkedChosenSource

@[expose] public section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical ContDiff
open CubicEisenstein InverseMoment
noncomputable section
namespace PrimeFamily
variable {ι : Type*} [Fintype ι] (P : PrimeFamily ι)

lemma fixed_active_sum_eq_mixed_of_controlled
    (_hP : Pairwise (Function.onFun IsCoprime P.ideal)) (j : ι→ℕ) (S : Finset ι)
    (φ : ActualEisensteinCubic.O→*ℂ) (c : ActualEisensteinCubic.O) (hc : c≠0) [Fintype (ActualEisensteinCubic.O⧸Ideal.span {c})]
    (G : ∀ h : ActualEisensteinCubic.O⧸Ideal.span {c}, FixedFourierGeometry c h)
    (N : ActualEisensteinCubic.O) (hN : ∀ h, (9:ActualEisensteinCubic.O)*(G h).c0∣N)
    (C : ∀ h : ActualEisensteinCubic.O⧸Ideal.span {c}, ∀ A : Finset ι,
      ControlledStratumArithmetic (fun i : A => P.generator i.val) N (G h).a0 (G h).c0 (G h).mode) (W : ℝ→ℂ) (X : ℝ) :
    (∑ t : FixedActiveCuspIndex c P.generator,
      fixedActiveFunctionWeight P.generator P.generator_ne_zero
        (mixedPrimeFunction P.generator P.generator_good j S) c hc φ t *
      (fixedActiveCuspDatum P.generator P.generator_ne_zero P.generator_primary c G N hN
        C t).smoothedKernel W X)=
    ∑ h : ActualEisensteinCubic.O⧸Ideal.span {c}, fixedThetaRowCoeff c hc φ h *
      ∑ A : Finset ι,
        localInactiveWeight P.generator P.generator_ne_zero (mixedPrimeFunction P.generator P.generator_good j S) A *
        mixedSmoothedValue (C h A) (hN h)
          (P.restrict A).generator_product_primary (G h).primary (G h).shape
          (P.restrict A).generator_ne_zero (G h).denominator_ne_zero (P.restrict A).generator_good
          (fun i => j i.val) (activeMarks A S) W X := by
  simp only [Fintype.sum_sigma, fixedActiveFunctionWeight, fixedActiveCuspDatum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h hh
  apply Finset.sum_congr rfl
  intro A hA
  simp only [mixedSmoothedValue,Finset.mul_sum]
  apply Finset.sum_congr (by grind)
  intro v hv
  rw [localActiveWeight_restrict]
  have hw : fullLocalFourierWeight (P.restrict A).generator_ne_zero
      (mixedPrimeFunction (P.restrict A).generator (P.restrict A).generator_good
        (fun i => j i.val) (activeMarks A S)) v =
      fullLocalFourierWeight (fun i : A => P.generator_ne_zero i.val)
        (mixedPrimeFunction (fun i : A => P.generator i.val) (fun i => P.generator_good i.val)
          (fun i => j i.val) (activeMarks A S)) v := rfl
  rw [hw]
  dsimp only [activeStratumDatum]
  ring

theorem marked_reflected_source_of_controlled
    (hP : Pairwise (Function.onFun IsCoprime P.ideal))
    (hodd : ∀ i, ringChar (ActualEisensteinCubic.O⧸P.ideal i)≠2) (j : ι→ℕ) (hj : ∀ i, j i<6) (S : Finset ι)
    (φ : ActualEisensteinCubic.O→*ℂ) (hφnorm : ∀ n, ‖φ n‖≤1)
    (Q : Ideal ActualEisensteinCubic.O) (hQ : Q≠0) (hφperiod : CanonicalCoefficientClass.FactorsModulo Q φ)
    (c : ActualEisensteinCubic.O) (hc : c≠0) [Fintype (ActualEisensteinCubic.O⧸Ideal.span {c})]
    (hcQ : Ideal.span {c}≤Ideal.span {(9:ActualEisensteinCubic.O)}*Q)
    (G : ∀ h : ActualEisensteinCubic.O⧸Ideal.span {c}, FixedFourierGeometry c h)
    (N : ActualEisensteinCubic.O) (hN : ∀ h, (9:ActualEisensteinCubic.O)*(G h).c0∣N)
    (C : ∀ h : ActualEisensteinCubic.O⧸Ideal.span {c}, ∀ A : Finset ι,
      ControlledStratumArithmetic (fun i : A => P.generator i.val) N (G h).a0 (G h).c0 (G h).mode)
    (W : ℝ→ℂ) (hWcompact : HasCompactSupport W)
    (lo hi : ℝ) (hlo : 0<lo) (hsupp : Function.support W⊆Set.Icc lo hi)
    (hW : ContDiff ℝ ∞ W) (X : ℝ) (hX : 0<X) :
    markedCompletedT (φ*unmarkedSexticTwist P.generator P.generator_good j S) W X
      (fun A => ∏ i∈S, if Ideal.span {P.generator i}∣A then 1 else 0)=
    thetaDerivativeScalar⁻¹*∑ h : ActualEisensteinCubic.O⧸Ideal.span {c}, fixedThetaRowCoeff c hc φ h *
      ∑ A : Finset ι,
        localInactiveWeight P.generator P.generator_ne_zero (mixedPrimeFunction P.generator P.generator_good j S) A *
        mixedReflectedValue (C h A) (G h).shape
          (P.restrict A).generator_ne_zero (G h).denominator_ne_zero (P.restrict A).generator_good
          (fun i => j i.val) (activeMarks A S) W X := by
  rw [P.marked_source_of_controlled hP j S φ hφnorm Q hQ hφperiod c hc hcQ G N hN C
    W hWcompact lo hi hlo hsupp hW X hX,
    P.fixed_active_sum_eq_mixed_of_controlled hP j S φ c hc G N hN C W X]
  congr 1
  apply Finset.sum_congr rfl
  intro h hh
  congr 1
  apply Finset.sum_congr rfl
  intro A hA
  congr 1
  apply mixed_smoothed_eq_reflected
  · intro i k hik
    change IsCoprime (Ideal.span {P.generator i.val}) (Ideal.span {P.generator k.val})
    rw [P.generator_span,P.generator_span]
    exact hP (by grind)
  · intro i
    rw [P.generator_span]
    exact hodd i.val
  · exact by grind
  · exact hlo
  · exact hsupp
  · exact hW
  · exact hX
end PrimeFamily
end
end SevenEighths.InverseReflectedPhase

end OAI
