module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularEquationSeparated
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.FDeriv.Congr
import Mathlib.Tactic
public import PDEFoundation.Calculus.RegularityOrder


/-! # The second velocity derivative of the literal angular separated test -/

 public section

namespace HypoellipticAleksandrov.KineticAleksandrov

open scoped Topology

/-- Every positive-position point is the literal angular point of its inverse coordinates. -/
theorem bellmanAngularPoint_inverse (q : ℝ × ℝ) (hq : 0 < q.1) :
    (bellmanAngularPoint (bellmanAngularHomeomorph.symm ⟨q, hq⟩)).val = q := congrArg Subtype.val (bellmanAngularHomeomorph.apply_symm_apply ⟨q, hq⟩)

variable (ζ φ : ℝ → ℝ)

/-- The first velocity formula holds throughout the open positive-position half-plane. -/
theorem bellmanSeparatedExpression_velocity_positive
    (hζ : Differentiable ℝ ζ) (hφ : Differentiable ℝ φ)
    (q : ℝ × ℝ) (hq : 0 < q.1) :
    fderiv ℝ (bellmanSeparatedExpression ζ φ) q (0, 1) =
      bellmanSeparatedExpression ζ (deriv φ) q / bellmanTestRadius q := by


  rw [← (bellmanAngularPoint_inverse q hq)]
  rw [bellmanSeparatedExpression_velocity ζ φ (bellmanAngularHomeomorph.symm ⟨q, hq⟩) (hζ _) (hφ _)]
  rw [bellmanSeparatedExpression, bellmanTestRadius_angularPoint,
    bellmanTestAngle_angularPoint]

/-- The second velocity derivative is exactly ζ(s)φ''(y)/s². -/
theorem bellmanSeparatedExpression_velocity_second
    (hζ : ContDiff ℝ PDE.smoothOrder ζ) (hφ : ContDiff ℝ PDE.smoothOrder φ)
    (w : BellmanPositiveTime × ℝ) :
    fderiv ℝ (fun q => fderiv ℝ (bellmanSeparatedExpression ζ φ) q (0, 1))
      (bellmanAngularPoint w).val (0, 1) =
      ζ w.1.val * deriv (deriv φ) w.2 / w.1.val ^ 2 := by

  have hs := bellmanSeparatedExpression_hasFDerivAt ζ (deriv φ) w
    (hζ.differentiable (by simp) _) (((contDiff_infty_iff_deriv.mp hφ).2).differentiable (by simp) _)

  have hi := (hasDerivAt_inv (by
      rw [bellmanTestRadius_angularPoint]
      exact w.1.property.ne')).comp_hasFDerivAt _
    (bellmanTestRadius_hasFDerivAt w)



  rw [((hs.mul hi).congr_of_eventuallyEq (by


      filter_upwards [(isOpen_lt continuous_const continuous_fst).mem_nhds (pow_pos w.1.property 3)] with q hqp
      rw [bellmanSeparatedExpression_velocity_positive ζ φ
        (hζ.differentiable (by simp)) (hφ.differentiable (by simp)) q hqp]
      rfl)).fderiv]
  simp only [bellmanSeparatedExpression, bellmanTestRadius_angularPoint,
    bellmanTestAngle_angularPoint, Function.comp_apply]
  change (ζ w.1.val * deriv φ w.2) *
      (-(w.1.val ^ 2)⁻¹ * (1 / (3 * w.1.val ^ 2) * 0)) +
    w.1.val⁻¹ * ((ζ w.1.val * deriv (deriv φ) w.2) *
      (w.1.val⁻¹ * 1 - w.2 / (3 * w.1.val ^ 3) * 0) +
      (deriv φ w.2 * deriv ζ w.1.val) * (1 / (3 * w.1.val ^ 2) * 0)) = _
  field_simp [w.1.property.ne']
  ring

end HypoellipticAleksandrov.KineticAleksandrov
