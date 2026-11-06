module

public import HypoellipticAleksandrov.Coefficients.Ellipticity
public import HypoellipticAleksandrov.Parabolic.ParabolicW12WeakDerivativeFamily

/-!
# Original-time equation for the canonical weight-two family

This file transports the literal equation of a selected parabolic W12 jet to
its canonical weak-derivative-family representatives.
-/

@[expose] public section

namespace HypoellipticAleksandrov.Parabolic

open MeasureTheory

variable {d : ℕ} {U : Set (TimeVelocity d)} (hU : IsOpen U) (J : ParabolicW12Function d U 2)

private theorem velocityTwo_comm  (i j : Fin d) :
    ParabolicDerivativeIndex.velocityTwo i j =
      ParabolicDerivativeIndex.velocityTwo j i := by
  apply Subtype.ext
  funext c
  cases c with
  | inl q => rfl
  | inr k =>
      by_cases hki : k = i
      · subst k
        by_cases hij : i = j
        · simp_all
        · simp [TimeVelocityMultiIndex.ofTimeVelocity, velocityCoord, hij]
      · by_cases hkj : k = j
        · subst k
          simp [TimeVelocityMultiIndex.ofTimeVelocity, velocityCoord, hki]
        · simp [TimeVelocityMultiIndex.ofTimeVelocity, hki, hkj]

private theorem representative_velocityTwo_ae_eq_velocityHessian
     (j i : Fin d) :
    (fun z =>
      (J.toWeakDerivativeFamily hU).representative
        (ParabolicDerivativeIndex.velocityTwo j i) z)
      =ᵐ[timeVelocityVolumeOn U]
        fun z => J.velocityHessian z j i := by
  rcases le_total j i with hji | hij
  · simp_all
  · rw [velocityTwo_comm j i,
      ParabolicW12Function.toWeakDerivativeFamily_representative_velocityTwo
        hU J i j hij]
    exact J.velocityHessian_ae_eq_swap hU i j

/-- The literal original-time equation of a selected local `W^{1,2}_2` jet
is preserved by its canonical weight-two weak-derivative family. -/
theorem ParabolicW12Function.toWeakDerivativeFamily_originalTimeEquation
    
    (a : CoefficientField d)
    (b : ℝ → PDE.Vec d → PDE.Vec d)
    (c F : ℝ → PDE.Vec d → ℝ)
    (hEq :
      (fun z =>
        J.timeDeriv z +
              (∑ i : Fin d, ∑ j : Fin d,
                a z.1 z.2 i j * J.velocityHessian z j i) +
            (∑ j : Fin d,
              b z.1 z.2 j * J.velocityGrad z j) +
          c z.1 z.2 * J.toFun z)
        =ᵐ[timeVelocityVolumeOn U]
          fun z => F z.1 z.2) :
    (fun z =>
      (J.toWeakDerivativeFamily hU).representative
          (ParabolicDerivativeIndex.timeOne d) z +
            (∑ i : Fin d, ∑ j : Fin d,
              a z.1 z.2 i j *
                (J.toWeakDerivativeFamily hU).representative
                  (ParabolicDerivativeIndex.velocityTwo j i) z) +
          (∑ j : Fin d,
            b z.1 z.2 j *
              (J.toWeakDerivativeFamily hU).representative
                (ParabolicDerivativeIndex.velocityOne j) z) +
        c z.1 z.2 *
          (J.toWeakDerivativeFamily hU).representative
            (ParabolicDerivativeIndex.zeroTwo d) z)
      =ᵐ[timeVelocityVolumeOn U]
        fun z => F z.1 z.2 := by
  have hhessian : ∀ᵐ z ∂timeVelocityVolumeOn U, ∀ i : Fin d, ∀ j : Fin d,
      (J.toWeakDerivativeFamily hU).representative
          (ParabolicDerivativeIndex.velocityTwo j i) z =
        J.velocityHessian z j i := by
    apply ae_all_iff.mpr
    intro i
    apply ae_all_iff.mpr
    intro j
    exact representative_velocityTwo_ae_eq_velocityHessian hU J j i
  filter_upwards [hEq, hhessian] with z hz hzhessian
  simp_all

end HypoellipticAleksandrov.Parabolic
