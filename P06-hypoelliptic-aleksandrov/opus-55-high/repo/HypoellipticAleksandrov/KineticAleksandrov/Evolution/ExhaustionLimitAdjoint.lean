module

public import HypoellipticAleksandrov.KineticAleksandrov.Occupation.ParabolicDuhamelSliceWeak

/-! # Smoothness and locality of regularized adjoint tests -/

@[expose] public section


namespace HypoellipticAleksandrov.KineticAleksandrov.Evolution

open HypoellipticAleksandrov Set

variable {n : ℕ} {B : FullKineticCoefficient n} {b : PDE.Vec n → PDE.Vec n}

/-- The regularized adjoint of a smooth compact test is smooth. -/
theorem contDiff_regularizedAdjoint  (hB : IsSmoothFullKineticCoefficient B)
    (hb : IsSmoothDrift b) {ψ : EvolutionVec n → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (ε : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (regularizedAdjoint B b ε ψ) := (Occupation.contDiff_transportedAdjoint hB hb hψ).add
    (contDiff_const.mul (ContDiff.sum fun l _ =>
      contDiff_fderiv_apply (contDiff_fderiv_apply hψ _) _))

/-- The regularized adjoint vanishes outside the original test support. -/
theorem regularizedAdjoint_eq_zero_of_notMem_tsupport  (ε : ℝ)
    (ψ : EvolutionVec n → ℝ) {x : EvolutionVec n} (hx : x ∉ tsupport ψ) :
    regularizedAdjoint B b ε ψ x = 0 := by
  have hzero (l : Fin n) :
      fderiv ℝ (fun y => fderiv ℝ ψ y (basisZ l)) x (basisZ l) = 0 := by
    apply image_eq_zero_of_notMem_tsupport
      (f := fun y => fderiv ℝ (fun z => fderiv ℝ ψ z _) y _)
    intro h
    exact hx (tsupport_evolution_fderiv_apply ψ _
      (tsupport_evolution_fderiv_apply _ _ h))
  simp only [regularizedAdjoint,
    Occupation.transportedAdjoint_eq_zero_of_notMem_tsupport ψ hx, hzero,
    Finset.sum_const_zero, mul_zero, add_zero]

end HypoellipticAleksandrov.KineticAleksandrov.Evolution
