module

public import OAI.NumberTheory.DirichletL.Descent.MixedRow

@[expose] public section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped Classical ContDiff
open CubicEisenstein
noncomputable section
noncomputable local instance activeReflectionQuotientFintype (P : Ideal ActualEisensteinCubic.O) [P.IsMaximal] :
    Fintype (ActualEisensteinCubic.O ⧸ P) := Fintype.ofFinite _

theorem markedCompletedT_fixed_active_strata {ι : Type*} [Fintype ι]
    (p : ι → ActualEisensteinCubic.O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hp : ∀ i, p i ≠ 0) (hprime : ∀ i, Prime (p i))
    (hprimary : ∀ i, ConcretePrimeRowBridge.goodLambda ^ 2 ∣ p i - 1)
    (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i}) (j : ι → ℕ) (S : Finset ι)
    (φ : ActualEisensteinCubic.O →* ℂ) (hφnorm : ∀ n, ‖φ n‖ ≤ 1)
    (Q : Ideal ActualEisensteinCubic.O) (hφperiod : CanonicalCoefficientClass.FactorsModulo Q φ)
    (c : ActualEisensteinCubic.O) (hc : c ≠ 0) [Fintype (ActualEisensteinCubic.O ⧸ Ideal.span {c})]
    (hcQ : Ideal.span {c} ≤ Ideal.span {(9 : ActualEisensteinCubic.O)} * Q)
    (G : ∀ h : ActualEisensteinCubic.O ⧸ Ideal.span {c}, FixedFourierGeometry c h) (N : ActualEisensteinCubic.O)
    (hN : ∀ h, (9 : ActualEisensteinCubic.O) * (G h).c0 ∣ N)
    (D : ∀ h : ActualEisensteinCubic.O ⧸ Ideal.span {c}, ∀ A : Finset ι,
      ControlledStratumArithmetic (fun i : A => p i.val) N (G h).a0 (G h).c0 (G h).mode)
    (call : ActualEisensteinCubic.O) (hcall : call ≠ 0) [Fintype (ActualEisensteinCubic.O ⧸ Ideal.span {call})]
    (hcallQ : Ideal.span {call} ≤ Ideal.span {(9 : ActualEisensteinCubic.O)} *
      ((Q * Ideal.span {∏ i, p i}) * Ideal.span {∏ i ∈ S, p i}))
    (W : ℝ → ℂ) (hWcompact : HasCompactSupport W)
    (lo hi : ℝ) (hlo : 0 < lo) (hsupp : Function.support W ⊆ Set.Icc lo hi)
    (hW : ContDiff ℝ ∞ W) (X : ℝ) (hX : 0 < X) :
    markedCompletedT (φ * unmarkedSexticTwist p hg j S) W X
      (fun A => ∏ i ∈ S, if Ideal.span {p i} ∣ A then 1 else 0) =
      thetaDerivativeScalar⁻¹ * ∑ t : FixedActiveCuspIndex c p,
        fixedActiveFunctionWeight p hp (mixedPrimeFunction p hg j S) c hc φ t *
          (fixedActiveCuspDatum p hp hprimary c G N hN D t).smoothedKernel W X := by
  have hnorm (n : ActualEisensteinCubic.O) : ‖(φ * unmarkedSexticTwist p hg j S) n‖ ≤ 1 := by
    rw [MonoidHom.mul_apply, norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (by grind)).trans
      (unmarkedSexticTwist_norm p hg j S n)
  have hperiod : CanonicalCoefficientClass.FactorsModulo (Q * Ideal.span {∏ i, p i})
      (φ * unmarkedSexticTwist p hg j S) := by
    intro x y hxy
    simp only [MonoidHom.mul_apply]
    rw [hφperiod x y (Ideal.mul_le_left hxy),
      unmarkedSexticTwist_periodic p hg j S x y (Ideal.mul_le_right hxy)]
  apply markedCompletedT_of_cusp_multiplier p S (by grind) _ hnorm _ hperiod
    call hcall hcallQ (fixedActiveCuspDatum p hp hprimary c G N hN D)
    (fixedActiveFunctionWeight p hp (mixedPrimeFunction p hg j S) c hc φ) ?_
    W hWcompact lo hi hlo hsupp hW X hX
  intro n
  rw [fixedActiveFunction_multiplier p hp hprimary (mixedPrimeFunction p hg j S)
    c hc G N hN D Q hcQ φ hφperiod,
    markedThetaQuotient_mk p S _ _ hperiod call hcallQ,
    fixedThetaTwist_mul, mixedPrimeFunction_product]
  ring

end
end SevenEighths.InverseMoment

end OAI
